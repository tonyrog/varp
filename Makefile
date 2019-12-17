#
# Simple make release helper
#
APP = varp
APPL = Varp
VSN = $(shell git describe --abbrev=0)
MACHINE = $(shell uname -m)

appimage:
	erl -wx -noshell -s varp_wx -s servator make_appimage $(APP) -s erlang halt
	strip $(APP).AppDir/bin/beam.smp
	strip $(APP).AppDir/bin/epmd
	strip $(APP).AppDir/bin/erlc
	strip $(APP).AppDir/bin/erl_child_setup
	strip $(APP).AppDir/bin/erlexec
	strip $(APP).AppDir/bin/escript
	strip $(APP).AppDir/bin/heart
	strip $(APP).AppDir/bin/inet_gethost
	appimagetool -n $(APP).AppDir
	mv $(APPL)-$(MACHINE).AppImage $(APPL)-$(VSN)-$(MACHINE).AppImage

# werl?
win32app:
	erl -wx -noshell -pa ../varp/ebin -s varp_wx -s servator make_win32app $(APP) -s erlang halt
	cp priv/$(APPL).exe $(APPL)-$(VSN)/

osxapp:
	erl -wx -noshell -s varp_wx -s servator make_osxapp $(APP) -s erlang halt
	mkdir -p tmpdist
	mv $(APPL).app tmpdist/
	cd tmpdist/
	../../servator/priv/make_icns ../priv/$(APP).png
	rm -rf AppIcon.iconset
	mv AppIcon.icns $(APPL).app/Contents/Resources/
	cd ..
	hdiutil create tmp.dmg -ov -volname "$(APPL)" -fs HFS+ -srcfolder "./tmpdist/"
	hdiutil convert -format UDZO -o $(APPL).dmg tmp.dmg

appimage_nw:
	erl -noshell -s $(APP) start0 -s servator make_appimage $(APP)
