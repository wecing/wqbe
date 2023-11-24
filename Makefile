.POSIX:
.SUFFIXES:
.SUFFIXES: .c .o

COMMON_OBJ = main.o ir.o parse.o util.o dephi.o
X64_OBJ = isel_naive.o ra_naive.o
OBJ = $(COMMON_OBJ) $(X64_OBJ)

SRCALL = $(OBJ:.o=.c)

CFLAGS = -std=c89 -g -Wall -Wextra -Wpedantic

wqbe: $(OBJ)
	$(CC) $(LDFLAGS) $(OBJ) -o $@

.c.o:
	$(CC) $(CFLAGS) -c $< -o $@

$(OBJ): all.h instr.inc
$(X64_OBJ): x64.h x64.inc

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
