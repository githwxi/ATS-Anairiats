#
#
# Makefile for ATS/Anairiats manual
#
#

manual_main.ps: \
  manual_def.tex \
  manual_preface.tex \
  manual_ats_basics.tex \
  manual_batch_compilation.tex \
  manual_macros.tex \
  manual_interaction_with_c.tex \
  manual_dependent_types.tex \
  manual_theorem_proving.tex \
  manual_linear_types.tex \
  manual_main.tex
	latex manual_main.tex; dvips -t letter -o manual_main.ps manual_main.dvi

manual_main.pdf: manual_main.ps; ps2pdf manual_main.ps

copy: manual_main.ps manual_main.pdf
	cp manual_main.ps manual_main.pdf ${HOME}/public_html/ATS/DOCUMENTATION/
	chmod 644 ${HOME}/public_html/ATS/DOCUMENTATION/manual_main.ps
	chmod 644 ${HOME}/public_html/ATS/DOCUMENTATION/manual_main.pdf

update:
	scp manual_main.ps manual_main.pdf \
          ats-hwxi,ats-lang@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/DOCUMENTATION

clean::
	rm -f *~

cleanall: clean
	rm -f manual_main.ps manual_main.pdf

###### end of [Makefile] ######
