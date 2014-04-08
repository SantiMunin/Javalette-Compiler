all:
	ghc --make -O2 Jlc.hs -o Jlc
bnfc:
	bnfc -d Javalette.cf
	happy -gca Javalette/Par.y
	alex -g Javalette/Lex.x
clean:
	rm -f Javalette/*.log Javalette/*.aux Javalette/*.hi Javalette/*.o Javalette/*.dvi
	rm -f Javalette/Doc.ps
	rm Frontend/*.hi Frontend/*.o Backend/*.hi Backend/*.o Internal/*.o Internal/*.hi
	rm Jlc.hi Jlc.o 

distclean:
	rm -rf Javalette
