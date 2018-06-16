CC ?= gcc
CFLAGS = -std=c99 -Wall -O2

unlambda: unlambda.c
	$(CC) $(CFLAGS) -o $@ $<

test: unlambda
	./run_tests ./unlambda

clean:
	rm -f unlambda
