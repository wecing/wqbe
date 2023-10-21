.POSIX:
.SUFFIXES:
.SUFFIXES: .c .o

OBJ = main.o ir.o parse.o util.o

SRCALL = $(OBJ:.o=.c)

CFLAGS = -std=c89 -g -Wall -Wextra -Wpedantic

wqbe: $(OBJ)
	$(CC) $(LDFLAGS) $(OBJ) -o $@

.c.o:
	$(CC) $(CFLAGS) -c $< -o $@

$(OBJ): all.h

clean:
	rm -f *.o wqbe

fmt:
	@for F in $(SRCALL);                       \
	do                                         \
		awk "{                             \
			if (\$$0 ~ /\\t/) 	   \
				printf(\"$$F:%d contains tab: %s\\n\", NR, \$$0); \
			if (\$$0 ~ / +\$$/) 	   \
				printf(\"$$F:%d line has trailing space: %s\\n\", NR, \$$0); \
			if (length(\$$0) > 80)     \
				printf(\"$$F:%d line too long: %s\\n\", NR, \$$0); \
		}" < $$F;                          \
	done

.PHONY: clean fmt
