#
# Simple make release helper
#
APP = varp
APPL = Varp
VSN = $(shell git describe --abbrev=0)
MACHINE = $(shell uname -m)

.PHONY: all test test-gui clean

all:
	(cd src && $(MAKE) all)
	(cd c_src && $(MAKE) all)

# build and run the eunit test suites
test: all
	(cd test && $(MAKE) test)

# the same, including the gui window (needs xvfb-run)
test-gui: all
	(cd test && $(MAKE) test-gui)

clean:
	(cd src && $(MAKE) clean)
	(cd c_src && $(MAKE) clean)
	(cd test && $(MAKE) clean)

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
	rm -rf tmpdist/$(APPL).app
	mv $(APPL).app tmpdist/
	(cd tmpdist/; ../../servator/priv/make_icns ../priv/$(APP).png)
	rm -rf tmpdist/AppIcon.iconset
	mv tmpdist/AppIcon.icns tmpdist/$(APPL).app/Contents/Resources/
	hdiutil create tmp.dmg -ov -volname "$(APPL)" -fs HFS+ -srcfolder "./tmpdist/"
	hdiutil convert -format UDZO -o $(APPL)-$(VSN).dmg tmp.dmg
	rm tmp.dmg

appimage_nw:
	erl -noshell -s $(APP) start0 -s servator make_appimage $(APP)
