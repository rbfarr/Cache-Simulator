#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#include "cachesim.h"

/*
 * Richard Farr (rfarr6)
 * ECE 4100
 *
 * Project 1
 */

/*
 * L1 and victim cache pointers
 */

static uint64_t* my_cache;
static uint64_t* victim_cache;

/*
 * Frequently used variables
 */ 

static uint64_t set_size, num_sets;
static uint64_t C, B, S, V, K;

/*
 * Gets the LRU ranking of a cache entry
 *
 * @e cache entry
 *
 * return: the LRU ranking, ranges from 0 to S-1
 */

inline uint64_t get_ranking(uint64_t e) {
    return e >> 3 & ~(~0 << S);
}

/*
 * Sets the LRU ranking of a cache entry
 *
 * @e cache entry pointer
 * @v new LRU value
 */

inline void set_ranking(uint64_t* e, uint64_t v) {
    *e &= ~(~(~0 << S) << 3);
    *e |= v << 3;
}

/*
 * Gets the dirty bit of a cache entry
 *
 * @e cache entry
 *
 * return: the dirty bit value (0 or 1)
 */

inline uint64_t get_dirty(uint64_t e) {
    return e >> 1 & 1;
}

/*
 * Sets the dirty bit of a cache entry
 *
 * @e cache entry pointer
 * @v new dirty bit value
 */

inline void set_dirty(uint64_t* e, uint64_t v) {
    *e &= ~(1 << 1);
    *e |= v << 1;
}

/*
 * Gets the valid bit of a cache entry
 *
 * @e cache entry
 *
 * return: the valid bit value (0 or 1)
 */

inline uint64_t get_valid(uint64_t e) {
    return e & 1;
}

/*
 * Sets the valid bit of a cache entry
 *
 * @e cache entry pointer
 * @v new valid bit value
 */

inline void set_valid(uint64_t* e, uint64_t v) {
    *e &= ~1;
    *e |= v;
}

/*
 * Gets the tag value of a cache entry
 *
 * @e cache entry
 *
 * return: the tag value, ranges from 0 to 2^(64-C+S)-1
 */

inline uint64_t get_cache_tag(uint64_t e) {
    return e >> (3+S) & ~(~0 << (64-C+S));
}

/*
 * Sets the tag value of a cache entry
 *
 * @e cache entry pointer
 * @v new tag value
 */

inline void set_cache_tag(uint64_t* e, uint64_t v) {
    *e &= ~(~0 << (3+S));
    *e |= v << (3+S);
}

/*
 * Gets the tag value of a victim cache entry
 *
 * @e victim cache entry
 *
 * return: the tag value, ranges from 0 to 2^(64-B)-1
 */

inline uint64_t get_victim_tag(uint64_t e) {
    return e >> 3 & ~(~0 << (64-B));
}

/*
 * Sets the tag value of a victim cache entry
 *
 * @e victim cache entry pointer
 * @v new tag value
 */

inline void set_victim_tag(uint64_t* e, uint64_t v) {
    *e &= ~(~0 << 3);
    *e |= v << 3;
}

/*
 * Gets the prefetched bit of a cache entry
 *
 * @e cache entry
 *
 * return: the prefetched bit (0 or 1)
 */

inline uint64_t get_prefetched(uint64_t e) {
    return e >> 2 & 1;
}

/*
 * Sets the prefetched bit of a cache entry
 *
 * @e cache entry pointer
 * @v new prefetched bit value
 */

inline void set_prefetched(uint64_t* e, uint64_t v) {
    *e &= ~(1 << 2);
    *e |= v << 2;
}

/*
 * Gets the L1 tag from an address
 *
 * @a address
 *
 * return: the L1 tag, ranges from 0 to 2^(64-C+S)-1
 */

inline uint64_t get_address_cache_tag(uint64_t a) {
    return a >> (C-S) & ~(~0 << (64-C+S));
}

/*
 * Gets the victim tag from an address
 *
 * @a address
 *
 * return: the victim tag, ranges from 0 to 2^(64-B)-1
 */

inline uint64_t get_address_victim_tag(uint64_t a) {
    return a >> B & ~(~0 << (64-B));
}

/*
 * Gets the L1 index from an address
 *
 * @a address
 *
 * return: the L1 index, ranges from 0 to 2^(C-B-S)-1
 */

inline uint64_t get_address_index(uint64_t a) {
    return a >> B & ~(~0 << (C-B-S));
}

/*
 * Gets the block address of an address
 *
 * @a address
 *
 * return: the block addres (address with block offset = 0)
 */

inline uint64_t get_block_addr(uint64_t a) {
    return a & (~0 << B);
}

/*
 * Reconstructs victim tag from L1 cache entry and its index
 *
 * @e cache entry
 * @n the index
 *
 * return: the victim tag, ranges from 0 to 2^(64-B)-1
 */

inline uint64_t cache_entry_to_victim_tag(uint64_t e, uint64_t n) {
    return get_cache_tag(e) << (C-B-S) | n;
}

/*
 * Converts victim cache entry to L1 cache tag
 *
 * @e victim cache entry
 *
 * return: the L1 cache tag, ranges from 0 to 2^(64-C+S)-1
 */

inline uint64_t victim_entry_to_cache_tag(uint64_t e) {
    return get_victim_tag(e) >> (C-B-S) & ~(~0 << 64-C+S);
}

/**
 * Subroutine for initializing the cache. You many add and initialize any global or heap
 * variables as needed.
 * XXX: You're responsible for completing this routine
 *
 * @c The total number of bytes for data storage is 2^C
 * @b The size of a single cache line in bytes is 2^B
 * @s The number of blocks in each set is 2^S
 * @v The number of blocks in the victim cache is V
 * @k The prefetch distance is K
 */
void setup_cache(uint64_t c, uint64_t b, uint64_t s, uint64_t v, uint64_t k) {

    // calculate # blocks = 2^C / 2^B
    uint64_t cache_blocks = 1 << (c-b);

    // calculate # sub caches = 2^S
    num_sets = 1 << s;

    // calculate # blocks in each sub cache = # blocks / # sub caches
    set_size = cache_blocks / num_sets;

    // Copy inputs to global variables for later use
    C = c;
    B = b;
    S = s;
    V = v;
    K = k;

    // Make sure L1 tag and victim tag lengths do not exceed available storage space in uint64_t

    // storing cache data as  [tag, lru_position, prefetched, dirty, valid]
    // storing victim data as [tag, prefetched, dirty, valid]

    if ((64-c+s) > (61-s) || (64-b) > 61) {
        fprintf(stderr, "maximum tag size exceeded\n");
        exit(1);
    }

    // Make sure cache parameters are valid

    if ((c-b) < s) {
        fprintf(stderr, "number of cache blocks cannot be less than size of set\n");
        exit(1);
    }

    // Allocate memory for tag storage

    if (!(my_cache = malloc(sizeof(uint64_t)*cache_blocks))) {
        fprintf(stderr, "unable to allocate enough space for cache\n");
        exit(1);
    }

    if (!(victim_cache = malloc(sizeof(uint64_t)*v))) {
        fprintf(stderr, "unable to allocate enough space for victim cache\n");
        exit(1);
    }
    
    // Initialize caches to 0

    memset(my_cache, 0, sizeof(uint64_t)*cache_blocks);
    memset(victim_cache, 0, sizeof(uint64_t)*v);
}

/*
 * Marks the specified entry as MRU
 *
 * @newest_entry: pointer to the newest entry
 * @ndx: The index of the newest entry's set
 */

void touch_cache_entry(uint64_t* newest_entry, uint64_t ndx) {
    uint64_t i, *cache_entry;
    uint64_t curr_ranking, temp_ranking;

    // Get current ranking of the entry
    curr_ranking = get_ranking(*newest_entry);

    /*
     * Loop through the set, ignore invalid entries, get the
     * ranking of each member of the set and increment if it
     * is less than the current ranking of the newest entry.
     * Set the ranking of the newest entry = 0
     */

    for (i = 0; i < num_sets; i++) {
        cache_entry = &my_cache[set_size*i+ndx];

        if (!get_valid(*cache_entry)) continue;

        temp_ranking = get_ranking(*cache_entry);

        if (temp_ranking < curr_ranking) {
            temp_ranking++;
        } else if (temp_ranking == curr_ranking) {
            temp_ranking = 0;
        }

        set_ranking(cache_entry, temp_ranking);
    }
}

/*
 * Determines the LRU entry in the set
 *
 * @ndx: The index of the set
 *
 * return: A pointer to the LRU entry
 */

uint64_t* find_lru_entry(uint64_t ndx) {
    uint64_t i, *cache_entry, *temp_entry = NULL;
    uint64_t temp_ranking, max_ranking = 0;

    /*
     * Loop through the set, ignore invalid entries.
     * If the ranking is higher than 0 and higher than
     * any previously encountered ranking, set it to max,
     * and set the return value equal to that entry
     */

    for (i = 0; i < num_sets; i++) {
        cache_entry = &my_cache[set_size*i+ndx];

        if (!get_valid(*cache_entry)) continue;

        temp_ranking = get_ranking(*cache_entry);

        if (temp_ranking >= max_ranking) {
            max_ranking = temp_ranking;
            temp_entry = cache_entry;
        }
    }

    return temp_entry;
}

/*
 * Constructs a victim cache entry and inserts it into the FIFO queue
 *
 * @victim_tag: The tag of the new victim entry
 * @dirty: The dirty bit of the new victim entry
 * @prefetched: The prefetched bit of the new victim entry
 * @p_stats: Pointer to the statistics structure
 */

void add_to_victim_cache(uint64_t victim_tag, uint64_t dirty, uint64_t prefetched, struct cache_stats_t* p_stats) {
    uint64_t i;

    // If last entry in the queue is valid and dirty, it counts as a writeback

    if (get_valid(victim_cache[V-1]) && get_dirty(victim_cache[V-1])) {
        p_stats->bytes_transferred += 1 << B;
        p_stats->write_backs++;

        set_dirty(&victim_cache[V-1], 0);
    }

    // Shift entires to the right

    for (i = V-1; i >= 1; i--) {
        victim_cache[i] = victim_cache[i-1];
    }

    // Overwrite first entry with new info

    set_victim_tag(&victim_cache[0], victim_tag);
    set_valid(&victim_cache[0], 1);

    set_dirty(&victim_cache[0], dirty);
    set_prefetched(&victim_cache[0], prefetched);
}

/*
 * Determines if an address exists in the L1 cache
 *
 * @address: The address
 *
 * return: The pointer to the entry or NULL
 */

uint64_t* exists_in_cache(uint64_t address) {
    uint64_t i, *cache_entry;

    // Get the index of the address
    uint64_t ndx = get_address_index(address);

    /*
     * Loop through the sets and determine if the
     * tag matches that of the address. If so, return
     * the pointer to that entry.
     */

    for (i = 0; i < num_sets; i++) {
        cache_entry = &my_cache[set_size*i+ndx];

        if (get_valid(*cache_entry) && get_address_cache_tag(address) == get_cache_tag(*cache_entry)) {
            return cache_entry;
        }
    }

    return NULL;
}

/*
 * Determines if an address exists in the victim cache
 *
 * @address: The address
 *
 * return: The pointer to the entry or NULL
 */

uint64_t* exists_as_victim(uint64_t address) {
    uint64_t i, *cache_entry;

    /*
     * Loop through the sets and determine if the
     * tag matches that of the address. If so, return
     * the pointer to that entry.
     */

    for (i = 0; i < V; i++) {
        cache_entry = &victim_cache[i];

        if (get_valid(*cache_entry) && get_address_victim_tag(address) == get_victim_tag(*cache_entry)) {            
            return cache_entry;
        }        
    }

    return NULL;
}

/**
 * Subroutine that simulates the cache one trace event at a time.
 * XXX: You're responsible for completing this routine
 *
 * @rw The type of event. Either READ or WRITE
 * @address  The target memory address
 * @p_stats Pointer to the statistics structure
 */
void cache_access(char rw, uint64_t address, struct cache_stats_t* p_stats) {

    // Get L1 index corresponding to the address
    uint64_t ndx = get_address_index(address);
    uint64_t *cache_entry, *lru_entry, temp_entry;

    uint64_t temp_addr, block_addr, d, i, j, prefetch = 0;

    // Static variables to keep track of the last missed address and the pending stride
    static uint64_t last_miss_block_addr = 0;
    static uint64_t pending_stride = 0;

    // Increment accesses
    p_stats->accesses++;

    // Increment r/w
    if (rw == READ) {
        p_stats->reads++;
    } else {
        p_stats->writes++;
    }

    /*
     * If the address is already in the cache, update its LRU ranking,
     * set the dirty bit if a write access, and check the prefetched bit
     * for a useful prefetch. Nothing left to do after this, so return.
     */

    if ((cache_entry = exists_in_cache(address))) {
        touch_cache_entry(cache_entry, ndx);
        if (rw == WRITE) set_dirty(cache_entry, 1);

        if (get_prefetched(*cache_entry)) {
            p_stats->useful_prefetches++;
            set_prefetched(cache_entry, 0);
        }

        return;
    }

    // L1 miss
    p_stats->misses++;

    // Increment r/w miss
    if (rw == READ) {
        p_stats->read_misses++;
    } else {
        p_stats->write_misses++;
    }

    /*
     * Check the victim cache for the address. If it exists, find the LRU
     * entry in the L1, overwrite it with the victim cache entry, check the
     * prefetched bit, update the LRU ranking, set the dirty bit if a write
     * access, and replace the victim cache entry with the old LRU entry.
     */

    if ((cache_entry = exists_as_victim(address))) {
        lru_entry = find_lru_entry(ndx);
        temp_entry = *lru_entry;

        set_cache_tag(lru_entry, victim_entry_to_cache_tag(*cache_entry));
        set_valid(lru_entry, 1);
        set_dirty(lru_entry, get_dirty(*cache_entry));
        set_prefetched(lru_entry, get_prefetched(*cache_entry));

        if (get_prefetched(*lru_entry)) {
            p_stats->useful_prefetches++;
            set_prefetched(lru_entry, 0);
        }

        touch_cache_entry(lru_entry, ndx);

        if (rw == WRITE) set_dirty(lru_entry, 1);
            
        set_victim_tag(cache_entry, cache_entry_to_victim_tag(temp_entry, ndx));
        set_valid(cache_entry, 1);

        set_dirty(cache_entry, get_dirty(temp_entry));
        set_prefetched(cache_entry, get_prefetched(temp_entry));

        // Skip the first iteration of the prefetch loop
        j = 1;
    } else {

        // VC miss
        p_stats->vc_misses++;

        // Increment VC r/w miss
        if (rw == READ) {
            p_stats->read_misses_combined++;
        } else {
            p_stats->write_misses_combined++;
        }

        // Miss in VC, so must insert the address into the L1
        j = 0;
    }

    // Calculate the block address
    block_addr = get_block_addr(address);

    // Calculate distance between the block address and the previously missed block address
    d = block_addr-last_miss_block_addr;

    // Update the last missed block address
    last_miss_block_addr = block_addr;

    // If the distance is the same as the last distance, prefetch
    if (d == pending_stride) prefetch = 1;

    // Update the pending stride distance for the next access
    pending_stride = d;

    /*
     * Loop through the number of prefetches, K. The first iteration is the inital insertion of
     * the address into the cache.
     */

    for (; j <= K; j++) {

        // If VC hit but no prefetch, don't loop
        if (j > 0 && !prefetch) break;

        // Determine address to prefetch and its L1 index
        temp_addr = address + j*d;
        ndx = get_address_index(temp_addr);

        // Increment bytes transferred
        p_stats->bytes_transferred += 1 << B;

        // j > 0 --> prefetch
        if (j > 0) {
            p_stats->prefetched_blocks++;

            /*
             * If prefetch address already exists in cache, skip this prefetch.
             *
             * If prefetch address exists as a victim cache entry, swap with the LRU
             * value (same as above), and skip this prefetch.
             */

            if ((cache_entry = exists_in_cache(temp_addr))) {
                continue;
            } else if ((cache_entry = exists_as_victim(temp_addr))) {
                lru_entry = find_lru_entry(ndx);
                temp_entry = *lru_entry;

                set_cache_tag(lru_entry, victim_entry_to_cache_tag(*cache_entry));                
                set_valid(lru_entry, 1);
                set_dirty(lru_entry, get_dirty(*cache_entry));
                set_prefetched(lru_entry, 1);

                set_victim_tag(cache_entry, cache_entry_to_victim_tag(temp_entry, ndx));
                set_valid(cache_entry, 1);

                set_dirty(cache_entry, get_dirty(temp_entry));
                set_prefetched(cache_entry, get_prefetched(temp_entry));

                continue;
            }
        }

        /*
         * Loop through the set, and search for unused locations. If location
         * is unused (not valid), insert the address tag, update its lru ranking,
         * prefetched bit, valid bit, and dirty bit. If not prefetching, convert entry
         * to MRU.
         */

        for (i = 0; i < num_sets; i++) {
            cache_entry = &my_cache[set_size*i+ndx];

            if (!get_valid(*cache_entry)) {
                set_cache_tag(cache_entry, get_address_cache_tag(temp_addr));
                set_ranking(cache_entry, i);
                set_prefetched(cache_entry, j > 0);
                set_valid(cache_entry, 1);
                set_dirty(cache_entry, 0);

                if (j == 0) {
                    touch_cache_entry(cache_entry, ndx);
                    if (rw == WRITE) set_dirty(cache_entry, 1);
                }

                break;
            }
        }

        // No open slots in the set

        if (i == num_sets) {

            // Find the LRU entry
            lru_entry = find_lru_entry(ndx);

            /*
             * If no victim cache, go ahead and count writeback
             * If one or more victim cache entries, put the LRU entry into the VC
             */

            if (V == 0) {
                if (get_dirty(*lru_entry)) {
                    p_stats->bytes_transferred += 1 << B;
                    p_stats->write_backs++;

                    set_dirty(lru_entry, 0);
                }
            } else {
                add_to_victim_cache(cache_entry_to_victim_tag(*lru_entry, ndx), get_dirty(*lru_entry), get_prefetched(*lru_entry), p_stats);
            }

            // Overwrite LRU entry with the new address
            set_cache_tag(lru_entry, get_address_cache_tag(temp_addr));
            set_prefetched(lru_entry, j > 0);
            set_valid(lru_entry, 1);
            set_dirty(lru_entry, 0);

            // If not a prefetch iteration, set the entry to MRU, and set the dirty bit if a write access
            if (j == 0) {
                touch_cache_entry(lru_entry, ndx);
                if (rw == WRITE) set_dirty(lru_entry, 1);
            }
        }
    }
}

/**
 * Subroutine for cleaning up any outstanding memory operations and calculating overall statistics
 * such as miss rate or average access time.
 * XXX: You're responsible for completing this routine
 *
 * @p_stats Pointer to the statistics structure
 */
void complete_cache(struct cache_stats_t *p_stats) {

    // Final statistics
	p_stats->hit_time = 2.0 + 0.2*S;
    p_stats->miss_penalty = 200;
    p_stats->miss_rate = (double)p_stats->misses / (double)p_stats->accesses;
    p_stats->avg_access_time = p_stats->hit_time + ((double)p_stats->vc_misses / (double)p_stats->accesses) * (double)p_stats->miss_penalty;

    // Free up the memory allocated for the caches
    free(my_cache);
    free(victim_cache);
}

