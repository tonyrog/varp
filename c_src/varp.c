/*
 *  varp.c --
 *
 *     Wrapper to start Varp on Windows.
 *
 *  Copyright (c) 2002-2011 Bjorn Gustavsson
 *  Copyright (c) 2013 Dan Gudmundsson
 *
 *  See the file "license.terms" for information on usage and redistribution
 *  of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 */

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#undef WIN32_LEAN_AND_MEAN
#include <shlobj.h>
#include <stdio.h>
#include <stdlib.h>
#include <shellapi.h>
#include <direct.h>

static void install(wchar_t* dir);
static int  need_install(wchar_t* dir);
static int  get_install_dir(wchar_t* dir);
static void print_path(FILE* fp, wchar_t* path);

int
WINAPI WinMain(HINSTANCE hInst, HINSTANCE hPrev, LPSTR szCmdLine, int sw)
{
  PROCESS_INFORMATION piProcInfo;
  STARTUPINFOW siStartInfo = {0};
  int argc;
  wchar_t** argv;
  wchar_t install_dir[MAX_PATH];
  wchar_t cmd_line[3*MAX_PATH];
  wchar_t pref_dir[MAX_PATH];
  char message[40];
  int i;
  int ok;
  int err;
  HKEY hkey;
  DWORD type;

  argv = CommandLineToArgvW(GetCommandLineW(), &argc);
  get_install_dir(install_dir);
  
  if (argc > 1 && wcscmp(argv[1], L"--install") == 0) {
      install(install_dir);
      exit(0);      
  }
  else if (need_install(install_dir)) {
      install(install_dir);
  }

  pref_dir[0] = L'\0';
  SHGetFolderPathW(NULL,CSIDL_APPDATA|CSIDL_FLAG_CREATE, NULL, 0, pref_dir);

  _snwprintf(cmd_line, 3*MAX_PATH, L"\"%s\\bin\\werl.exe\" -smp enable", install_dir);
  i=0;
  if ((argc > 1 && wcscmp(argv[1], L"--debug") == 0)) {
      i++;
      _snwprintf(cmd_line+wcslen(cmd_line), 3*MAX_PATH,  L" -run varp_wx start");
  } else {
      _snwprintf(cmd_line+wcslen(cmd_line), 3*MAX_PATH,  L" -detached");
      _snwprintf(cmd_line+wcslen(cmd_line), 3*MAX_PATH,  L" -run varp_wx start");
  }

  if (argc > (1+i)) {
      _snwprintf(cmd_line+wcslen(cmd_line), 3*MAX_PATH, L" \"%s\"", argv[1+i]);
  }

  // fprintf(stderr, "Cmd %S\r\n", cmd_line);
  siStartInfo.cb = sizeof(STARTUPINFO); 
  siStartInfo.wShowWindow = SW_MINIMIZE;
  siStartInfo.dwFlags = STARTF_USESHOWWINDOW;

  ok = CreateProcessW(NULL, 
		      cmd_line, 
		      NULL, 
		      NULL, 
		      FALSE,
		      0,
		      NULL,
		      NULL,
		      &siStartInfo,
		      &piProcInfo);
  if (!ok) {
    sprintf(message, "Failed to start Varp: %u", GetLastError());
    MessageBox(NULL, message, NULL, MB_OK);
  }
  exit(0);
}

static int get_install_dir(wchar_t* dir)
{
  HANDLE module = GetModuleHandle(NULL);
  int i;
  
  if (module == NULL) {
    MessageBox(NULL, "Fatal: Failed to get module handle", NULL, MB_OK);
    exit(1);
  }
  if (GetModuleFileNameW(module, dir, MAX_PATH) == 0) {
    MessageBox(NULL, "Fatal: Failed to get module file name", NULL, MB_OK);
    exit(1);
  }

  i = wcslen(dir) - 1;
  while (i >= 0 && dir[i] != L'\\') {
    --i;
  }
  dir[i] = L'\0';
  return 1;
}
    
static int need_install(wchar_t* dir)
{
    wchar_t inifile[MAX_PATH];
    FILE* fp;
    
    _snwprintf(inifile, MAX_PATH,  L"%s/bin/erl.ini", dir);    
    if ((fp = _wfopen(inifile, L"r")) == NULL)
	return 1;
    fclose(fp);
    return 0;
}

static void install(wchar_t* dir)
{
    // wchar_t curdir[MAX_PATH];
    wchar_t inifile[MAX_PATH];    
    FILE* fp;

    // _wgetcwd(curdir, MAX_PATH);
    _snwprintf(inifile, MAX_PATH,  L"%s/bin/erl.ini", dir);

    if ((fp = _wfopen(inifile, L"w")) == NULL) {
	MessageBox(NULL, "Failed to install Erlang/OTP components", NULL, MB_OK);
	exit(1);
    }
    fprintf(fp, "[erlang]\n");
    fprintf(fp, "Bindir=");
    print_path(fp, dir);
    fprintf(fp, "\\\\bin\n");
    fprintf(fp, "Progname=erl\n");
    fprintf(fp, "Rootdir=");
    print_path(fp, dir);
    putc('\n', fp);
    fclose(fp);
}

static void print_path(FILE* fp, wchar_t* path)
{
    int c;

    while ((c = *path) != 0) {
	if (c != '\\') {
	    fputwc(c, fp);
	} else {
	    fputwc('\\', fp);
	    fputwc('\\', fp);
	}
	path++;
    }
}
