
MODULES = \
	varp_scan \
	varp_parse \
	prover \
	varc \
	varc_prop \
	varc_test \
	varp \
	carp \
	varp_test \
	varp_example \
	varp_bench \
	pred \
	bdd \
	dimacs \
	cnf \
	formula \
	example \
	form_md5 \
	form_sha1 \
	form \
	aa  \
	sudoku


EBIN = ../ebin
ERLC = erlc

include ../vsn.mk
VSN=$(VARP_VSN)

APP_NAME= varp
APP_FILE= $(APP_NAME).app
APP_SRC= $(APP_FILE).src
APP_TARGET= $(EBIN)/$(APP_FILE)

override ERLC_FLAGS = # +native


OBJS = $(MODULES:%=$(EBIN)/%.beam)

TARGET_FILES = $(OBJS) $(APP_TARGET)

debug: ERLC_FLAGS += -Ddebug 

all: $(TARGET_FILES)

all32: $(TARGET_FILES)

debug: all

release: all

depend:
	edep -MM -o ../ebin $(ERLC_FLAGS) $(MODULES:%=%.erl) > depend.mk

dialyze:
	dialyzer --src -o dia.out $(ERLC_FLAGS) -c $(MODULES:%=%.erl) 

edoc:
	erl -noshell -pa doc -run edoc_run application "varp" '".."' '[{private,true},no_packages,{sort_functions,false}]'
##erl -noshell -run edoc_run application "'$(APP_NAME)'"

clean:
	rm -f $(OBJS)

$(APP_TARGET): $(APP_SRC) ../vsn.mk
	sed -e 's;%VSN%;$(VSN);'  $< > $@

-include depend.mk

varp_parse.erl: varp_parse.yrl
	$(ERLC) $(ERLC_FLAGS) -o $@ $<

varp_scan.erl: varp_scan.xrl
	$(ERLC) $(ERLC_FLAGS) -o $@ $<

$(EBIN)/%.beam:	%.erl
	$(ERLC) $(ERLC_FLAGS) -o $(EBIN) $<
