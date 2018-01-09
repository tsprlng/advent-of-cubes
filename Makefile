.PHONY : all clean

all : allColors

allColors : Main.hs Solver.hs Pieces.hs
	ghc -o $@ -O Main.hs -hidir .crap -odir .crap

clean :
	rm -rf .crap
