CC ?= gcc
CFLAGS = -std=c99 -Wall -O2
PREFIX = /usr/local

unlambda: unlambda.c
	$(CC) $(CFLAGS) -o $@ $<

test: unlambda
	./run_tests ./unlambda

install: unlambda
	mkdir -p $(PREFIX)/bin
	cp $< $(PREFIX)/bin/

uninstall:
	rm -f $(PREFIX)/bin/unlambda

clean:
	rm -f unlambda

.PHONY: test install uninstall clean
