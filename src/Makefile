all: normal

normal:
	ghc --make -O2 Jlc.hs -o Jlc
	cp executable ../jlc
wall:	
	ghc -W -fno-warn-name-shadowing --make -O2 Jlc.hs -o Jlc
	cp executable ../jlc
bnfc:
	bnfc -d Javalette.cf
	happy -gca Javalette/Par.y
	alex -g Javalette/Lex.x
clean:
	rm -f Javalette/*.log Javalette/*.aux Javalette/*.hi Javalette/*.o Javalette/*.dvi
	rm -f Javalette/Doc.ps
	rm -f Javalette/*.bak
	rm -f Frontend/*.hi Frontend/*.o Backend/*.hi Backend/*.o Internal/*.o Internal/*.hi
	rm -f Jlc.hi Jlc.o 

distclean:
	rm -rf Javalette
