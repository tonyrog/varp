import os

def erlpath():
    s = os.popen("erl -noshell -eval \"io:format('~s',[code:root_dir()])\" -s erlang halt")
    p = s.read()
    s.close()
    return p.rstrip()

def vsn():
    s = os.popen("git describe --tags --abbrev=0")
    p = s.read()
    s.close()
    return p.rstrip()

from distutils.core import setup, Extension
setup(name = 'varpy',
      version = vsn(),
      url = "http://www.rogvall.se/apps",
      author = "Tony Rogvall",
      author_email = "tony@rogvall.se",
      description = "Varpy Package",
      packages = ['varpy'],
      ext_modules = [
          Extension(name = 'varc',
                    define_macros = [("PYNIF",None),
                                     ("PYNIFNAME","varc"),
                                     ("STATIC_ERLANG_DRIVER", None)],
                    include_dirs = [erlpath()+"/usr/include"],
                    sources = ['c_src/varc_nif.c','c_src/pynif.c'])])
