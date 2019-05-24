#
# For building tigerats
#

CMAKE_MINIMUM_REQUIRED (VERSION 2.8)
PROJECT (TIGERATS C)

SET (CMAKE_MODULE_PATH $ENV{ATSHOME}/share/CMake)

FIND_PACKAGE (ATS REQUIRED)
IF (NOT ATS_FOUND)
MESSAGE (FATAL_ERROR ”ATS is not found!”)
ENDIF ()

ATS_COMPILE (
TIGERATS_SRC
tigerats_main.dats
error.sats
error.dats
stamp.sats
stamp.dats
symbol.sats
symbol.dats
types.sats
types.dats
absyn.sats
absyn.dats
fixity.sats
fixity.dats
parser.sats
parser.dats
tychecker.sats
tychecker.dats
interp0.sats
interp0.dats
templab.sats
templab.dats
irtree.sats
irtree.dats
frame.sats
frame.dats
translate.sats
translate.dats
canonical.sats
canonical.dats
interp1.sats
interp1.dats
assem.sats
assem.dats
codegen.sats
codegen.dats
fgnode.sats
fgnode.dats
tempset.sats
tempset.dats
fgraph.sats
fgraph.dats
igraph.sats
igraph.dats
liveness.dats
regalloc.sats
regalloc.dats
PARCOMB/posloc.sats
PARCOMB/posloc.dats
PARCOMB/parcomb.sats
PARCOMB/parcomb.dats
PARCOMB/tokenize.sats
PARCOMB/tokenize.dats
LIB/funmap_avltree.dats
LIB/hashtable.dats
LIB/linmap_randbst.dats
) # end of [ATS_COMPILE]

ADD_EXECUTABLE (tigcomp ${TIGERATS_SRC})
