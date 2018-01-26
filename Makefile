.PHONY : all clean

all : cli gfx

cli : Main-CommandLine.hs Solver.hs Pieces.hs
	ghc -o $@ -O Main-CommandLine.hs -hidir .crap -odir .crap

gfx : Main-GLFW.hs Solver.hs Pieces.hs
	ghc -o $@ -O Main-GLFW.hs -hidir .crap -odir .crap

clean :
	rm -rf .crap gfx cli
