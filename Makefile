.PHONY : all clean

all : cli gfx cube.js

cli : Main-CommandLine.hs Solver.hs Pieces.hs
	stack exec -- ghc -o $@ -O Main-CommandLine.hs -hidir .crap -odir .crap

gfx : Main-GLFW.hs Solver.hs Pieces.hs Cube.hs
	stack exec -- ghc -o $@ -O Main-GLFW.hs -hidir .crap -odir .crap

cube.js : Main-WebGL.hs Solver.hs Pieces.hs Cube.hs
	stack exec -- hastec Main-WebGL.hs -o cube.js --debug --onexec --own-namespace --with-js=worker-ns-patch.js -odir .crap -hidir .crap --outdir=.crap

clean :
	rm -rf .crap gfx cli cube.js *.hi *.o *.jsmod
