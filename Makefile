.PHONY : all clean

all : cli gfx cube.html

cli : Main-CommandLine.hs Solver.hs Pieces.hs
	ghc -o $@ -O Main-CommandLine.hs -hidir .crap -odir .crap

gfx : Main-GLFW.hs Solver.hs Pieces.hs
	ghc -o $@ -O Main-GLFW.hs -hidir .crap -odir .crap

cube.html : Main-WebGL.hs Solver.hs Pieces.hs
	hastec --output-html Main-WebGL.hs -o cube.html --opt-whole-program=on --opt-minify=on --outdir=.crap

clean :
	rm -rf .crap gfx cli *.html *.hi *.o
