
gui.so: gui.h gui.cpp encoding.hpp createEncoding.hpp createEncoding.cpp logo.xpm
	clang++ $$(wx-config --cflags --libs core, base, adv) -fpic -shared -o gui.so gui.cpp createEncoding.cpp

logo.xpm: make_logo.scm ../logo.svg
	gimp -i -b - < make_logo.scm
	sed -i "s/char/const char/" logo.xpm

.PHONY: clean

clean:
	rm gui.so logo.xpm

