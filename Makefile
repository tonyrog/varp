#
# Simple make helper
#

#	erl -wx -noshell -s varp_wx -s servator make_appimage varp -s erlang halt
appimage:
	erl -s varp_wx -s servator make_appimage varp -s erlang halt
	strip varp.AppDir/bin/beam.smp
	strip varp.AppDir/bin/epmd
	strip varp.AppDir/bin/erlc
	strip varp.AppDir/bin/erl_child_setup
	strip varp.AppDir/bin/erlexec
	strip varp.AppDir/bin/escript
	strip varp.AppDir/bin/heart
	strip varp.AppDir/bin/inet_gethost
	appimagetool -n varp.AppDir

appimage_nw:
	erl -noshell -s varp start0 -s servator make_appimage varp
