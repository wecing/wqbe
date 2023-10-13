CFLAGS = -std=c89 -g -Wall -Wextra -Wpedantic

wqbe: main.c
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f wqbe

.PHONY: clean
