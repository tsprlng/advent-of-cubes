.PHONY : all clean

all : cli gfx cube.js

cli : Main-CommandLine.hs Solver.hs Pieces.hs
	ghc -o $@ -O Main-CommandLine.hs -hidir .crap -odir .crap

gfx : Main-GLFW.hs Solver.hs Pieces.hs Cube.hs
	ghc -o $@ -O Main-GLFW.hs -hidir .crap -odir .crap

cube.js : Main-WebGL.hs Solver.hs Pieces.hs Cube.hs
	hastec Main-WebGL.hs -o cube.js --opt-whole-program=on --opt-minify=on

clean :
	rm -rf .crap gfx cli cube.js *.hi *.o
