
SOURCES = gui.cpp

WARNINGS = -Werror -Wall -Wextra -Wpedantic -Weverything -Wno-c++98-compat -Wno-padded -Wno-global-constructors -Wno-exit-time-destructors -Wno-c++2a-compat -Wno-c++98-c++11-c++14-c++17-compat-pedantic -Wno-float-equal

NANAPATH = $(HOME)/nana

NANAINC = $(NANAPATH)/include
NANALIB = $(NANAPATH)

INCS = -I$(NANAINC)
LIBS = -L$(NANALIB) -lnana -lX11 -lXcursor -lpthread -lrt -lXft -lpng -lasound -lfontconfig

CHECKS = -*,clang-analyzer-*,cppcoreguidelines-*,misc-*,modernize-*,performance-*,portability-*,readability-*,-cppcoreguidelines-pro-type-reinterpret-cast,-*-magic-numbers

gui.so: gui.h gui.cpp draw.hpp encoding.hpp createEncoding.hpp logo.xpm
	clang++-10 -MJ compile_commands.json -std=c++20 $(WARNINGS) -fPIC -shared -o gui.so $(SOURCES) $(INCS) $(LIBS)
	sed -i -e '1s/^/[/' -e '$$s/,$$/]/' compile_commands.json
	clang-tidy-10 $(SOURCES) -warnings-as-errors=* -checks=$(CHECKS)

logo.xpm: make_logo.scm ../logo.svg
	gimp -i -b - < make_logo.scm
	sed -i "s/char/const char/" logo.xpm

.PHONY: clean

clean:
	rm gui.so logo.xpm

