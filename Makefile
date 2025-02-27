.PHONY : all clean

all : cli gfx

cli : Main-CommandLine.hs Solver.hs Pieces.hs
	cabal build cli

gfx : Main-GLFW.hs Solver.hs Pieces.hs Cube.hs
	cabal build gfx

cube.js : Main-WebGL.hs Solver.hs Pieces.hs Cube.hs
	hastec Main-WebGL.hs -o cube.js --opt-whole-program=on --opt-minify=on --onexec --own-namespace --with-js=worker-ns-patch.js -odir .crap -hidir .crap --outdir=.crap

clean :
	rm -rf .crap gfx cli cube.js *.hi *.o *.jsmod
