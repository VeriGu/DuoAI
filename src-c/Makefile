CC = g++
CFLAGS = -Wall -O2 -std=c++17

default: main

main: main.o basics.o preprocessing.o StringProcessor.o Helper.o Solver.o InvRefiner.o CounterexampleHandler.o InvEncoder.o
	$(CC) $(CFLAGS) -pthread -o main main.o basics.o preprocessing.o StringProcessor.o Helper.o Solver.o InvRefiner.o CounterexampleHandler.o InvEncoder.o

main.o: main.cpp Solver.h
	$(CC) $(CFLAGS) -c main.cpp

basics.o: basics.cpp basics.h
	$(CC) $(CFLAGS) -c basics.cpp

preprocessing.o: preprocessing.cpp preprocessing.h
	$(CC) $(CFLAGS) -c preprocessing.cpp

StringProcessor.o: StringProcessor.cpp StringProcessor.h
	$(CC) $(CFLAGS) -c StringProcessor.cpp

Helper.o: Helper.cpp Helper.h
	$(CC) $(CFLAGS) -c Helper.cpp

Solver.o: Solver.cpp Solver.h
	$(CC) $(CFLAGS) -c Solver.cpp

InvRefiner.o: InvRefiner.cpp InvRefiner.h
	$(CC) $(CFLAGS) -c InvRefiner.cpp

CounterexampleHandler.o: CounterexampleHandler.cpp CounterexampleHandler.h
	$(CC) $(CFLAGS) -c CounterexampleHandler.cpp

InvEncoder.o: InvEncoder.cpp InvEncoder.h
	$(CC) $(CFLAGS) -c InvEncoder.cpp

clean:
	rm *.o main