######
#
# A simple Makefile
#
######

.PHONY: all

######

all::

######

all:: all_AUP
all_AUP: ; make -C AUP all

all:: all_INTRO
all_INTRO: ; make -C INTRO all

all:: all_MISC
all_MISC: ; make -C MISC all
all:: all_MISC_Twentyfour
all_MISC_Twentyfour: ; make -C MISC/Twentyfour all
all:: all_MISC_HttpServer
all_MISC_HttpServer: ; make -C MISC/HttpServer all

all:: all_MULTICORE
all_MULTICORE: ; make -C MULTICORE all

all:: all_PCPV
all_PCPV: ; make -C PCPV all

all:: all_SOCKET
all_SOCKET: ; make -C SOCKET all

all:: all_TEST
all_TEST: ; make -C TEST all

all:: all_cairo
all_cairo: ; make -C cairo all

all:: all_GTK
all_GTK: ; make -C GTK all

all:: all_ProjectEuler
all_ProjectEuler: ; make -C ProjectEuler all

#all:: all_SCRIPTING
#all_SCRIPTING: ; make -C SCRIPTING all

all:: all_SHOOTOUT
all_SHOOTOUT: ; make -C SHOOTOUT all

all:: all_SHOOTOUT_SUBMIT
all_SHOOTOUT_SUBMIT: ; make -C SHOOTOUT/SUBMIT all

######

INTRO::
	make -C INTRO xref
	cp INTRO/INTRO.html INTRO/INTRO
	cp INTRO/Makefile INTRO/INTRO
	cp INTRO/HelloWorld.dats INTRO/INTRO
	cp INTRO/HelloWorld_dats.html INTRO/INTRO
	cp INTRO/f91.dats INTRO/INTRO
	cp INTRO/f91_dats.html INTRO/INTRO
	cp INTRO/fact1.dats INTRO/INTRO
	cp INTRO/fact1_dats.html INTRO/INTRO
	cp INTRO/fact2.dats INTRO/INTRO
	cp INTRO/fact2_dats.html INTRO/INTRO
	cp INTRO/fact3.dats INTRO/INTRO
	cp INTRO/fact3_dats.html INTRO/INTRO
	cp INTRO/fact4.dats INTRO/INTRO
	cp INTRO/fact4_dats.html INTRO/INTRO
	cp INTRO/fact_in_c.dats INTRO/INTRO
	cp INTRO/fact_in_c_dats.html INTRO/INTRO
	cp INTRO/fibs.dats INTRO/INTRO
	cp INTRO/fibs_dats.html INTRO/INTRO
	cp INTRO/revarr.dats INTRO/INTRO
	cp INTRO/revarr_dats.html INTRO/INTRO
	cp INTRO/revstr.dats INTRO/INTRO
	cp INTRO/revstr_dats.html INTRO/INTRO
	cp INTRO/tally.dats INTRO/INTRO
	cp INTRO/tally_dats.html INTRO/INTRO
	scp -r INTRO/INTRO ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE
	scp -r INTRO/XREF ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/INTRO

INTRO_html::
	scp -r INTRO/INTRO.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/INTRO

######

MISC::
	make -C MISC xref
	cp MISC/MISC.html MISC/MISC
	cp MISC/Makefile MISC/MISC
	cp MISC/AutoDiff.dats MISC/MISC
	cp MISC/AutoDiff_dats.html MISC/MISC
	cp MISC/coin_flip.dats MISC/MISC
	cp MISC/coin_flip_dats.html MISC/MISC
	cp MISC/curve.dats MISC/MISC
	cp MISC/curve_dats.html MISC/MISC
	cp MISC/fft.dats MISC/MISC
	cp MISC/fft_dats.html MISC/MISC
	cp MISC/GarsiaWachs.dats MISC/MISC
	cp MISC/GarsiaWachs_dats.html MISC/MISC
	cp MISC/GaussElim.dats MISC/MISC
	cp MISC/GaussElim_dats.html MISC/MISC
	cp MISC/kmp.dats MISC/MISC
	cp MISC/kmp_dats.html MISC/MISC
	cp MISC/gcd_mt.dats MISC/MISC
	cp MISC/gcd_mt_dats.html MISC/MISC
	cp MISC/longestline.dats MISC/MISC
	cp MISC/longestline_dats.html MISC/MISC
	cp MISC/passwdgen.dats MISC/MISC
	cp MISC/passwdgen_dats.html MISC/MISC
	cp MISC/pi_lazy.dats MISC/MISC
	cp MISC/pi_lazy_dats.html MISC/MISC
	cp MISC/queens.dats MISC/MISC
	cp MISC/queens_dats.html MISC/MISC
	cp MISC/queens_lazy_vt.dats MISC/MISC
	cp MISC/queens_lazy_vt_dats.html MISC/MISC
	cp MISC/quicksort_list.dats MISC/MISC
	cp MISC/quicksort_list_dats.html MISC/MISC
	cp MISC/quicksort2_list.dats MISC/MISC
	cp MISC/quicksort2_list_dats.html MISC/MISC
	cp MISC/sieve_lazy.dats MISC/MISC
	cp MISC/sieve_lazy_dats.html MISC/MISC
	cp MISC/strmat.dats MISC/MISC
	cp MISC/strmat_dats.html MISC/MISC
	cp MISC/systemf_programming_examples.dats MISC/MISC
	cp MISC/systemf_programming_examples_dats.html MISC/MISC
	cp MISC/tetrix.dats MISC/MISC
	cp MISC/tetrix_dats.html MISC/MISC
	cp MISC/wc.dats MISC/MISC
	cp MISC/wc_dats.html MISC/MISC
	scp -r MISC/MISC ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE
	scp -r MISC/XREF ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/MISC

MISC_html::
	scp -r MISC/MISC.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/MISC

######

AUP::
	make -C AUP xref
	cp AUP/Makefile AUP/AUP
	cp AUP/*.?ats AUP/AUP
	cp AUP/*_?ats.html AUP/AUP
	scp -r AUP/AUP ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE
	scp -r AUP/XREF ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/AUP

AUP_html::
	scp -r AUP/AUP.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/AUP

######

SOCKET::
	make -C SOCKET xref
	cp SOCKET/Makefile SOCKET/SOCKET
	cp SOCKET/daytime_tcpclient.dats SOCKET/SOCKET
	cp SOCKET/daytime_tcpclient_dats.html SOCKET/SOCKET
	cp SOCKET/daytime_tcpserver.dats SOCKET/SOCKET
	cp SOCKET/daytime_tcpserver_dats.html SOCKET/SOCKET
	cp SOCKET/echo_tcpclient.dats SOCKET/SOCKET
	cp SOCKET/echo_tcpclient_dats.html SOCKET/SOCKET
	cp SOCKET/echo_tcpserver.dats SOCKET/SOCKET
	cp SOCKET/echo_tcpserver_dats.html SOCKET/SOCKET
	cp SOCKET/echo_preforking.dats SOCKET/SOCKET
	cp SOCKET/echo_preforking_dats.html SOCKET/SOCKET
	scp -r SOCKET/SOCKET ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE
	scp -r SOCKET/XREF ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/SOCKET

SOCKET_html::
	scp -r SOCKET/SOCKET.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/SOCKET

######

MULTICORE::
	make -C MULTICORE xref
	cp MULTICORE/Makefile MULTICORE/MULTICORE
	cp MULTICORE/*.?ats MULTICORE/MULTICORE
	cp MULTICORE/*_?ats.html MULTICORE/MULTICORE
	scp -r MULTICORE/MULTICORE ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE
	scp -r MULTICORE/XREF ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/MULTICORE

MULTICORE_html::
	scp -r MULTICORE/MULTICORE.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/MULTICORE

######

GTK::
	make -C GTK xref
	cp GTK/Makefile GTK/GTK
	cp GTK/GameOf24.dats GTK/GTK
	cp GTK/GameOf24_dats.html GTK/GTK
	cp GTK/gtkcairoclock.dats GTK/GTK
	cp GTK/gtkcairoclock_dats.html GTK/GTK
	cp GTK/gtkcairopascal.dats GTK/GTK
	cp GTK/gtkcairopascal_dats.html GTK/GTK
	cp GTK/bsearch_demo_dats.html GTK/GTK
	cp GTK/bsearch_demo_dats.html GTK/GTK
	scp -r GTK/GTK ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE
	scp -r GTK/XREF ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/GTK

GTK_html::
	scp -r GTK/GTK.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/GTK

######

LF::
	make -C LF xref
	cp LF/Makefile LF/LF
	cp LF/BinaryTree.dats LF/LF
	cp LF/BinaryTree_dats.html LF/LF
	cp LF/ClosureConv.dats LF/LF
	cp LF/ClosureConv_dats.html LF/LF
	cp LF/CPS.dats LF/LF
	cp LF/CPS_dats.html LF/LF
	cp LF/CutElimILL.dats LF/LF
	cp LF/CutElimILL_dats.html LF/LF
	cp LF/KolmogorovTrans.dats LF/LF
	cp LF/KolmogorovTrans_dats.html LF/LF
	cp LF/HilbertCalculus.dats LF/LF
	cp LF/HilbertCalculus_dats.html LF/LF
	cp LF/irrationality-of-sqrt2.dats LF/LF
	cp LF/irrationality-of-sqrt2_dats.html LF/LF
	cp LF/mini-ML.dats LF/LF
	cp LF/mini-ML_dats.html LF/LF
	cp LF/naive-set.dats LF/LF
	cp LF/naive-set_dats.html LF/LF
	cp LF/pigeonhole.dats LF/LF
	cp LF/pigeonhole_dats.html LF/LF
	cp LF/STLC-foas.dats LF/LF
	cp LF/STLC-foas_dats.html LF/LF
	cp LF/STLC-SN-foas.dats LF/LF
	cp LF/STLC-SN-foas_dats.html LF/LF
	cp LF/STLC-SN-hoas.dats LF/LF
	cp LF/STLC-SN-hoas_dats.html LF/LF
	scp -r LF/LF ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE
	scp -r LF/XREF ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/LF

LF_html::
	scp -r LF/LF.html ats-hwxi,ats-lang@web.sourceforge.net:htdocs/EXAMPLE/LF

###### end of [Makefile] ######
