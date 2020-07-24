import os

def erlpath():
    s = os.popen("erl -noshell -eval \"io:format('~s',[code:root_dir()])\" -s erlang halt")
    p = s.read()
    s.close()
    return p

from distutils.core import setup, Extension
setup(name = 'varpy',
      version = '0.9.20',
      url = "http://www.rogvall.se/apps",
      author = "Tony Rogvall",
      author_email = "tony@rogvall.se",
      description = "Varpy Package",
      packages = ['varpy'],
      ext_modules = [
          Extension(name = 'varc',
                    define_macros = [("PYNIF",None),
                                     ("PYNIFNAME","varc")],
                    include_dirs = [erlpath()+"/usr/include"],
                    sources = ['c_src/pynif.c','c_src/varc_nif.c'])])
