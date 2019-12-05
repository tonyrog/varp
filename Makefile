#
# Simple make release helper
#
VSN = $(shell git describe)
MACHINE = $(shell uname -a)

appimage:
	erl -wx -noshell -s varp_wx -s servator make_appimage varp -s erlang halt
	strip varp.AppDir/bin/beam.smp
	strip varp.AppDir/bin/epmd
	strip varp.AppDir/bin/erlc
	strip varp.AppDir/bin/erl_child_setup
	strip varp.AppDir/bin/erlexec
	strip varp.AppDir/bin/escript
	strip varp.AppDir/bin/heart
	strip varp.AppDir/bin/inet_gethost
	appimagetool -n varp.AppDir
	mv Varp-$(MACHINE).AppImage Varp-$(VSN)-$(MACHINE).AppImage

# werl?
win32app:
	erl -wx -noshell -pa ../varp/ebin -s varp_wx -s servator make_win32app varp -s erlang halt
	cp priv/Varp.exe Varp-$(VSN)/

appimage_nw:
	erl -noshell -s varp start0 -s servator make_appimage varp
