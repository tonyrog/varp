# pento: the formula generator (pento.erl) and the epx board (pento_epx.erl)
# varp is built in .., epx is expected next to varp (override EPX=...)
EPX ?= $(HOME)/erlang/epx
ERLC_FLAGS = +debug_info

all: pento.beam pento_epx.beam

%.beam: %.erl
	erlc $(ERLC_FLAGS) -o . $<

run: all
	erl -noshell -pa . -pa ../ebin -pa $(EPX)/ebin -eval 'pento_epx:run()'

shell: all
	erl -pa . -pa ../ebin -pa $(EPX)/ebin

clean:
	rm -f *.beam
