#
# Simple make helper
#

appimage:
	erl -wx -noshell -s varp_wx -s servator make_appimage varp

appimage_nw:
	erl -noshell -s varp start0 -s servator make_appimage varp
