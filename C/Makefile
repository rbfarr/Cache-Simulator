CXXFLAGS = -g -Wall -Werror -Wextra -pedantic -std=c++0x -lm
CXX=gcc

all: cachesim

cachesim: cachesim.o cachesim.h cachesim_driver.o
	$(CXX) $(CXXFLAGS) -o cachesim cachesim.o cachesim_driver.o

clean:
	rm -f cachesim *.o

.PHONY: all clean
