
SOURCE = gui.cpp createEncoding.cpp

WARNINGS = -Werror -Wall -Wextra -Wpedantic -Weverything -Wno-c++98-compat -Wno-padded

#CHECKS = -*,clang-analyzer-*,cppcoreguidelines-*,misc-*,modernize-*,performance-*,portability-*,readability-*
CHECKS = -*,clang-analyzer-*,misc-*,modernize-*,performance-*,portability-*,readability-*

gui.so: gui.h gui.cpp encoding.hpp createEncoding.hpp createEncoding.cpp logo.xpm
	clang++ -MJ compile_commands.json ${WARNINGS} $$(wx-config --cflags --libs core, base, adv) -fpic -shared -o gui.so ${SOURCE}
	sed -i -e '1s/^/[/' -e '$$s/,$$/]/' compile_commands.json
	clang-tidy ${SOURCE} -warnings-as-errors=* -checks=${CHECKS}

logo.xpm: make_logo.scm ../logo.svg
	gimp -i -b - < make_logo.scm
	sed -i "s/char/const char/" logo.xpm

.PHONY: clean

clean:
	rm gui.so logo.xpm

