# Needs raylib installed (apt: libraylib-dev, brew: raylib, MSYS2: mingw-w64-x86_64-raylib)
CC      ?= gcc
CFLAGS  = -std=c99 -Wall -Wextra -O2
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
  LIBS = -lraylib -framework OpenGL -framework Cocoa -framework IOKit -framework CoreVideo
else ifneq (,$(findstring MINGW,$(UNAME_S))$(findstring MSYS,$(UNAME_S)))
  LIBS = -lraylib -lopengl32 -lgdi32 -lwinmm
else
  LIBS = -lraylib -lGL -lm -lpthread -ldl -lrt -lX11
endif

main: main.c
	$(CC) $(CFLAGS) main.c -o main $(LIBS)

run: main
	./main

clean:
	rm -f main
