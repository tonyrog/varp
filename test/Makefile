#
# Build and run the varp eunit test suites
#
ERLC="$(shell which erlc)"
ERL="$(shell which erl)"
EBIN=./ebin
ERLC_FLAGS=-I ../src -pa ../ebin +debug_info

TEST_SOURCES=varp_tc.erl $(wildcard *_tests.erl)
TEST_OBJECTS=$(TEST_SOURCES:%.erl=$(EBIN)/%.beam)
TEST_MODULES=$(basename $(wildcard *_tests.erl))

all: $(TEST_OBJECTS)

$(EBIN)/%.beam: %.erl
	@mkdir -p $(EBIN)
	$(ERLC) $(ERLC_FLAGS) -o $(EBIN) $<

test: all
	$(ERL) -noshell -pa ../ebin -pa $(EBIN) \
	  -eval 'case eunit:test([$(subst $(space),$(comma),$(TEST_MODULES))],[verbose]) of ok -> halt(0); _ -> halt(1) end.'

# same, but also starts the gui window, in an Xvfb of its own
test-gui: all
	VARP_TEST_GUI=1 xvfb-run -a $(ERL) -noshell -pa ../ebin -pa $(EBIN) \
	  -eval 'case eunit:test([$(subst $(space),$(comma),$(TEST_MODULES))],[verbose]) of ok -> halt(0); _ -> halt(1) end.'

clean:
	rm -rf $(EBIN)

comma=,
empty=
space=$(empty) $(empty)

.PHONY: all test test-gui clean
