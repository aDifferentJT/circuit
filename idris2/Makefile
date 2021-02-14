./build/exec/adder: $(shell find . -type f -name "*.idr")
	idris2 -p contrib -o adder adder.idr

adder.dot: ./build/exec/adder
	$< graph $@

adder.png: adder.dot
	dot -Tpng -o$@ $<

.PHONY: show_graph

show_graph: adder.png
	feh adder.png

