######
#
# A simple Makefile for updating various ATS docs
#
######

all:: ATS
all:: TUTORIAL
all:: EXAMPLE
all:: EXAMPLES_new
all:: IMPLEMENT
all:: RESOURCE
all:: LIBRARY
all:: PAPER
all:: CHANGELOG

######

ATS::
	scp ATS.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/htdocs-old/ATS.html

FAQ::
	scp FAQ.txt \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/htdocs-old/FAQ.txt

TUTORIAL::
	scp TUTORIAL/tutorial.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/htdocs-old/TUTORIAL/tutorial.html

EXAMPLE::
	scp EXAMPLE/example.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/htdocs-old/EXAMPLE/example.html

EXAMPLE_new::
	scp EXAMPLE/example_new.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/htdocs-old/EXAMPLE/example_new.html

IMPLEMENT::
	scp IMPLEMENT/implement.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/htdocs-old/IMPLEMENT/implement.html

IMPLEMENT/ATSOPT::
	scp -r IMPLEMENT/ATSOPT \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/htdocs-old/IMPLEMENT

RESOURCE::
	scp RESOURCE/resource.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/htdocs-old/RESOURCE/resource.html

LIBRARY::
	scp LIBRARY/library.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/htdocs-old/LIBRARY/library.html

PAPER::
	scp PAPER/paper.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/htdocs-old/PAPER/paper.html

CHANGELOG::
	scp CHANGELOG/changelog.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/htdocs-old/CHANGELOG/changelog.html

######

sysprog::
	scp BOOK/sysprog.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/htdocs-old/DOCUMENT/sysprog.html

atsgrammar::
	scp \
          DOCUMENT/ATS_GRAMMAR/ats_grammar_desc.html \
          DOCUMENT/ATS_GRAMMAR/ats_grammar_yats.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/htdocs-old/DOCUMENT/GRAMMAR/

###### end of [Makefile] ######
