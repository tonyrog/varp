%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    wx GUI for varp
%%%
%%%   Note on build wxWidgets-3.0.4 from source
%%%   ./configure --with-opengl --enable-unicode --enable-graphics_ctx \
%%%     --enable-gnomeprint --disable-shared
%%%
%%% @end
%%% Created : 15 Sep 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_wx).

-include_lib("wx/include/wx.hrl").

-export([start/0, start/1]).
-export([main_loop/1]).

-export([output_model/4]).  %% varp callback

%% warp_wx is also a plugin (monitor assignment etc)
-behaviour(varp_plugin).
-export([options/0, run/2]).

%% debug export
-export([format_time/1]).

%% -define(DEBUG, true).
-include("varp.hrl").

-define(STCMOD, stc_modified).

-define(ID_EXPORT_CNF, 100).
-define(ID_EXPORT_SNF, 101).

-define(BJK(I,Name), [profile,(I),options,backjump,Name]).
-define(SAT(I,Name), [profile,(I),options,saturate,Name]).

-record(s,
	{
	 window,
	 splitter,
	 meta,
	 formula,
	 modified = false, %% formula modified
	 error    = false, %% error is marked
	 model,
	 satisfy,
	 falsify,
	 cancel,
	 settings,
	 dir = "",
	 export_dir = "",
	 filename = undefined,
	 path = undefined,
	 wx_env,            %% environment passed to plugin
	 %% menus
	 menu_save,         %% wxMenu
	 %% settings map
	 setting_widgets,   %% Name => Widget
	 setting_values,    %% Name => Value
	 %% config
	 setting_panel,     %% NoteBook/Frame
	 setting_apply,     %% wxButton apply settings
	 setting_cancel,    %% wxButton cancel settings
	 config_max_models, %% wxSpinCtrl
	 config_timeout,    %% wxSpinCtrl
	 config_saturate,   %% wxSpinCtrl (saturate=1 or none=0)
	 config_profile,    %% wxChoice 0..9
 	 config_nbound,     %% wxGauge
	 config_notebook
	}).

-define(SORT(Ord,Ord2),
	{order,[{sort,[(Ord),(Ord2)]},{seed,0}]}).

-define(REORDER_NONE,
	[
	]).

-define(REORDER_0,
	[
	 {1,?SORT(degree,random)},
	 {2,?SORT(rank,random)},
	 {3,?SORT(random,random)}
	]).

-define(REORDER_1,
	[
	 {1,?SORT(random,undefined)}
	]).

version() ->
    {ok,Vsn} = application:get_key(varp, vsn),
    Vsn.

start() ->
    start([]).

start(Bound) ->
    application:ensure_all_started(varp),
    application:load(wx),
    start_win_reg(),
    spawn(
      fun() ->
	      %% put('_wx_object_', {?MODULE,'_wx_init_'}),
	      Wx = wx:new(),
	      %% try wx:batch(fun() -> create_window(Wx) end) of
	      try create_window(Wx, Bound) of
		  S ->
		      wxWindow:show(S#s.window),
		      register_process(),
		      ?MODULE:main_loop(S),
		      wx:destroy()
	      catch
		  ?EXCEPTION(error,Reason,Trace) ->
		      io:format("error:~w\n~p\n", [Reason,?GET_STACK(Trace)])
	      end
      end).

create_window(Wx, Bound) ->
    Window = wxFrame:new(Wx, -1, "Varp", [{size, {900,600}}]),

    Path = code:priv_dir(varp),
    wxFrame:setIcon(Window,  wxIcon:new(filename:join(Path,"varp.png"),
					[{type, ?wxBITMAP_TYPE_PNG}])),

    wxFrame:createStatusBar(Window,[]),
    ok = wxFrame:connect(Window, close_window, [{skip,false}]),
    ok = wxFrame:connect(Window, command_menu_selected, []),

    MenuBar  = wxMenuBar:new(),
    FileM    = wxMenu:new([]),
    EditM    = wxMenu:new([]),
    HelpM    = wxMenu:new([]),

    % unlike wxwidgets the stock menu items still need text to be given,
    % although help text does appear

    %% FileMenu
    _NewMenuItem     = wxMenu:append(FileM, ?wxID_NEW, "&New\tCtrl+N"),
    _OpenMenuItem    = wxMenu:append(FileM, ?wxID_OPEN, "&Open...\tCtrl+O"),
    SaveMenuItem     = wxMenu:append(FileM, ?wxID_SAVE, "&Save\tCtrl+S"),
    _SaveAsMenuItem  = wxMenu:append(FileM, ?wxID_SAVEAS, "&Save As..."),
    _Sep1            = wxMenu:appendSeparator(FileM),
    _ExportCnf       = wxMenu:append(FileM, ?ID_EXPORT_CNF, "&Export CNF..."),
    _ExportSnf       = wxMenu:append(FileM, ?ID_EXPORT_SNF, "&Export SNF..."),
    _Sep2            = wxMenu:appendSeparator(FileM),
    _QuitMenuItem    = wxMenu:append(FileM, ?wxID_EXIT, "&Quit\tCtrl+Q"),

    %% Edit menu
    _Cut             = wxMenu:append(EditM, ?wxID_CUT, "&Cut\tCtrl+X"),
    _Copy            = wxMenu:append(EditM, ?wxID_COPY, "&Copy\tCtrl+C"),
    _Paste           = wxMenu:append(EditM, ?wxID_PASTE, "&Paste\tCtrl+V"),
    _Clear           = wxMenu:append(EditM, ?wxID_CLEAR, "&Clear\tDelete"),
    _SelectAll       = wxMenu:append(EditM, ?wxID_SELECTALL, "&Select All\tCtrl+A"),

    % Note the keybord accelerator
    _AboutMenuItem = wxMenu:append(HelpM, ?wxID_ABOUT, "&About...\tF1"),

    wxMenuItem:enable(SaveMenuItem,[{enable,false}]),

    wxMenu:appendSeparator(HelpM),
    ContentsMenuItem = wxMenu:append(HelpM, ?wxID_HELP_CONTENTS, "&Contents"),
    wxMenuItem:enable(ContentsMenuItem, [{enable, false}]),

    wxMenuBar:append(MenuBar, FileM, "&File"),
    wxMenuBar:append(MenuBar, EditM, "&Edit"),
    wxMenuBar:append(MenuBar, HelpM, "&Help"),
    wxFrame:setMenuBar(Window, MenuBar),

    FixedFont = wxFont:new(10, ?wxFONTFAMILY_TELETYPE, ?wxNORMAL, ?wxNORMAL,[]),
    %SmallFont = wxFont:new(8, ?wxFONTFAMILY_TELETYPE, ?wxNORMAL, ?wxNORMAL,[]),

    MainSizer = wxBoxSizer:new(?wxVERTICAL),
    Splitter = wxSplitterWindow:new(Window, []),
    Win1 = wxPanel:new(Splitter, []),
    Win2 = wxPanel:new(Splitter, []),

    wxSplitterWindow:splitHorizontally(Splitter, Win1, Win2),
    wxSplitterWindow:setSashGravity(Splitter, 0.1),
    wxSplitterWindow:setMinimumPaneSize(Splitter, 100),
    wxSplitterWindow:setSashPosition(Splitter, 300),

    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    %% WINDOW 1
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    MetaBox = wxStaticBoxSizer:new(?wxVERTICAL, Win1, [{label, "meta"}]),
    
    MetaVal = string:trim(
		lists:concat(
		  lists:append([ [Var,"=",Value," "] || 
				   {Var,Value} <- lists:reverse(Bound)]))),
    Meta = wxTextCtrl:new(Win1, 1, [{value, MetaVal},
				    {style, ?wxDEFAULT}]),
    Formula = wxStyledTextCtrl:new(Win1),
    wxStyledTextCtrl:styleSetFont(Formula, ?wxSTC_STYLE_DEFAULT, FixedFont),
    wxStyledTextCtrl:setLexer(Formula, ?wxSTC_LEX_CPP),
    wxStyledTextCtrl:setMarginType(Formula, 0, ?wxSTC_MARGIN_NUMBER),
    LW = wxStyledTextCtrl:textWidth(Formula, ?wxSTC_STYLE_LINENUMBER, "999"),
    wxStyledTextCtrl:setMarginWidth(Formula, 0, LW),
    wxStyledTextCtrl:setMarginWidth(Formula, 1, 0),
    wxStyledTextCtrl:setSelectionMode(Formula, ?wxSTC_SEL_LINES),
    wxStyledTextCtrl:setScrollWidth(Formula, 1),
    wxStyledTextCtrl:setCaretLineBackAlpha(Formula, 127),
    %% FIXME! Find better mode for VARP!
    Styles =  [{?wxSTC_C_DEFAULT,     {0,0,0}},
	       {?wxSTC_C_COMMENT,     {160,53,35}},
	       {?wxSTC_C_COMMENTLINE, {160,53,35}},
	       {?wxSTC_C_IDENTIFIER,  {150,100,40}},
	       {?wxSTC_C_NUMBER,      {5,5,100}},
	       {?wxSTC_C_STRING,      {170,45,132}},
	       {?wxSTC_C_OPERATOR,    {30,0,0}}
	      ],
    SetStyle = fun({Style, Color}) ->
		       wxStyledTextCtrl:styleSetFont(Formula, Style, FixedFont),
		       wxStyledTextCtrl:styleSetForeground(Formula, Style, Color)
	       end,
    [SetStyle(Style) || Style <- Styles],

    wxStyledTextCtrl:setKeyWords(Formula, 1, keyWords()),

    Policy = ?wxSTC_CARET_SLOP bor ?wxSTC_CARET_JUMPS bor ?wxSTC_CARET_EVEN,
    wxStyledTextCtrl:setYCaretPolicy(Formula, Policy, 3),
    wxStyledTextCtrl:setVisiblePolicy(Formula, Policy, 3),
    wxStyledTextCtrl:setReadOnly(Formula, false),

    Sizer1 = wxBoxSizer:new(?wxVERTICAL),
    wxSizer:add(MetaBox, Meta,  [{flag, ?wxEXPAND}]),
    wxSizer:add(Sizer1, MetaBox, [{flag, ?wxEXPAND}]),
    wxSizer:addSpacer(Sizer1, 10),
    wxSizer:add(Sizer1, Formula, [{flag, ?wxEXPAND}, {proportion, 1}]),

    wxStyledTextCtrl:connect(Formula,?STCMOD),
    wxStyledTextCtrl:connect(Formula,set_focus, [{skip,true}]),
    wxStyledTextCtrl:connect(Formula,left_down, [{skip,true}]),
    wxStyledTextCtrl:connect(Formula,key_down, [{skip,true}]),

    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    %% WINDOW 2
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    Sizer2 = wxBoxSizer:new(?wxVERTICAL),

    %% BUTTONS
    Run = wxStaticBoxSizer:new(?wxHORIZONTAL,Win2,[{label, "Run"}]),
    Satisfy = wxButton:new(Win2, ?wxID_ANY, [{label,"Satisfy"}]),
    wxButton:connect(Satisfy, command_button_clicked),
    wxButton:enable(Satisfy),

    Falsify = wxButton:new(Win2, ?wxID_ANY, [{label,"Falsify"}]),
    wxButton:connect(Falsify, command_button_clicked),
    wxButton:enable(Falsify),

    Cancel = wxButton:new(Win2, ?wxID_ANY, [{label,"Cancel"}]),
    SELF = self(),
    wxButton:connect(Cancel, command_button_clicked,
		     [{callback,
		       fun(_Event,_Object) ->
			       SELF ! {cancel, self()}
		       end }]),
    wxButton:disable(Cancel),

    wxSizer:add(Run, Satisfy, []),
    wxSizer:add(Run, Falsify, []),
    wxSizer:add(Run, Cancel, []),

    %% CONFIG max models
    MaxBox = wxStaticBoxSizer:new(?wxVERTICAL,Win2,[{label, "Max"}]),
    MaxModels = wxSpinCtrl:new(Win2, [{min,1},{max,1000}]),
    %% wxSpinCtrl:setRange(MaxModels, 1, 1000),
    wxSizer:add(MaxBox, MaxModels, [{flag, ?wxEXPAND}]),

    TimeBox = wxStaticBoxSizer:new(?wxVERTICAL,Win2,[{label,"Timeout"}]),
    Timeout = wxSpinCtrl:new(Win2, []),
    wxSpinCtrl:setRange(Timeout, 0, 100000),
    wxSizer:add(TimeBox, Timeout, [{flag, ?wxEXPAND}]),

    SaturateBox = wxStaticBoxSizer:new(?wxVERTICAL,Win2,[{label,"Saturate"}]),
    Saturate = wxSpinCtrl:new(Win2, []),
    wxSpinCtrl:setRange(Saturate, 0, 3),
    wxSizer:add(SaturateBox, Saturate, [{flag, ?wxEXPAND}]),

    ProfileBox = wxStaticBoxSizer:new(?wxHORIZONTAL,Win2,[{label,"Profile"}]),
    Profile = wxChoice:new(Win2, ?wxID_ANY,
			   [{choices,
			     ["1","2","3","4","5","6","7","8","9","10"]}
			   ]),
    wxChoice:setSelection(Profile, 0),
    wxChoice:connect(Profile, command_choice_selected),
    wxChoice:enable(Profile),
    wxSizer:add(ProfileBox, Profile,[{flag, ?wxEXPAND}]),

    SettingsBox = wxStaticBoxSizer:new(?wxHORIZONTAL,Win2,[{label,"Settings"}]),
    Settings = wxButton:new(Win2, ?wxID_ANY, [{label,"..."}]),
    wxButton:connect(Settings, command_button_clicked),
    wxButton:enable(Settings),
    wxSizer:add(SettingsBox, Settings, [{flag, ?wxEXPAND}]),

    %% View number of bound variables
    NBound = wxGauge:new(Win2, ?wxID_ANY, 100, [{size,{800,10}},
						{style,
						 ?wxGA_HORIZONTAL+
						     ?wxGA_SMOOTH}]),
    Config = wxBoxSizer:new(?wxVERTICAL),
    Config1 = wxBoxSizer:new(?wxHORIZONTAL),
    wxSizer:add(Config, Config1, []),
    wxSizer:add(Config, NBound, []),
    wxSizer:add(Config1, Run, [{proportion,3}]),
    wxSizer:add(Config1, MaxBox, [{proportion,1}]),
    wxSizer:add(Config1, TimeBox, [{proportion,1}]),
    wxSizer:add(Config1, SaturateBox, [{proportion,1}]),
    wxSizer:add(Config1, ProfileBox, [{proportion,1}]),
    wxSizer:add(Config1, SettingsBox, [{proportion,1}]),

    %% MODEL output window
    Model = wxStyledTextCtrl:new(Win2),
    wxStyledTextCtrl:styleSetFont(Model, ?wxSTC_STYLE_DEFAULT, FixedFont),
    wxStyledTextCtrl:setLexer(Model, ?wxSTC_LEX_NULL),
    wxStyledTextCtrl:setMarginType(Model, 0, ?wxSTC_MARGIN_NUMBER),
    LW = wxStyledTextCtrl:textWidth(Model, ?wxSTC_STYLE_LINENUMBER, "999"),
    wxStyledTextCtrl:setMarginWidth(Model, 0, LW),
    wxStyledTextCtrl:setMarginWidth(Model, 1, 0),
    wxStyledTextCtrl:setScrollWidth(Model, 1),
    wxStyledTextCtrl:setSelectionMode(Model, ?wxSTC_SEL_LINES),
    Policy = ?wxSTC_CARET_SLOP bor ?wxSTC_CARET_JUMPS bor ?wxSTC_CARET_EVEN,
    wxStyledTextCtrl:setYCaretPolicy(Model, Policy, 3),
    wxStyledTextCtrl:setVisiblePolicy(Model, Policy, 3),
    wxStyledTextCtrl:setReadOnly(Model, true),

    wxSizer:add(Sizer2, Config, []),
    wxSizer:add(Sizer2, Model,  [{flag, ?wxEXPAND}, {proportion, 1}]),

    %% Setup toplevel sizers
    wxSizer:add(MainSizer, Splitter, [{flag,?wxEXPAND},{proportion,1}]),

    wxPanel:setSizer(Win1, Sizer1),
    wxPanel:setSizer(Win2, Sizer2),

    ok = wxFrame:setStatusText(Window,lists:flatten(["Varp-",version()]),[]),
    wxFrame:connect(Window, command_splitter_sash_pos_changed),

    wxFrame:setTitle(Window, "Untitled"),

    SettingValues = varp_wx_settings:load(),
    {SettingPanel,Notebook,SettingApply,SettingCancel,SettingWidgets} =
	varp_wx_settings:create(Window,SettingValues),
    profile_update(Profile, SettingValues),
    wxSizer:add(MainSizer, SettingPanel, [{flag,?wxEXPAND},{proportion,1}]),
    wxPanel:hide(SettingPanel),

    wxFrame:setSizer(Window, MainSizer),

    {ok, DefaultDir} = file:get_cwd(), %% fixme: save dir?

    #s { window = Window,
	 splitter = Splitter,
	 meta = Meta,
	 formula = Formula,
	 model = Model,
	 falsify = Falsify,
	 satisfy = Satisfy,
	 cancel  = Cancel,
	 settings = Settings,
	 filename = undefined,
	 path = undefined,
	 dir = DefaultDir,
	 setting_widgets   = SettingWidgets,
	 setting_values    = SettingValues,
	 config_max_models = MaxModels,
	 config_timeout    = Timeout,
	 config_saturate   = Saturate,
	 config_profile    = Profile,	 
	 config_nbound     = NBound,
	 wx_env            = wx:get_env(),
	 setting_panel     = SettingPanel,
	 config_notebook   = Notebook,
	 setting_apply     = SettingApply,
	 setting_cancel    = SettingCancel,
	 menu_save         = SaveMenuItem
       }.

main_loop(S) ->
    receive
	Event when is_record(Event, wx) ->
	    try handle_event(Event, S) of
		{noreply, S1} ->
		    ?MODULE:main_loop(S1);
		{stop, Reason, S1} ->
		    {Reason, S1}
	    catch
		?EXCEPTION(error,Reason,Trace) ->
		    io:format("error:~w\n~p\n", [Reason,?GET_STACK(Trace)]),
		    error
	    end;
        _Msg ->
            ?dbg("Got ~p ~n", [_Msg]),
            ?MODULE:main_loop(S)
    end.

handle_event(Event, S) ->
    case Event of
        #wx{event=#wxClose{}} ->
	    ?dbg("CLOSE\n",[]),
	    if S#s.modified ->
		    case save_before(S, "Save before close") of
			{ok,S1} ->
			    wxFrame:destroy(S1#s.window),
			    {stop, ok, S1};
			{cancel,S1} ->
			    {noreply, S1}
		    end;
	       true ->
		    {stop, ok, S}
	    end;

        #wx{id=?wxID_EXIT, event=#wxCommand{type=command_menu_selected}} ->
	    ?dbg("EXIT\n",[]),
	    if S#s.modified ->
		    case save_before(S, "Save before exit") of
			{ok,S1} ->
			    wxWindow:destroy(S1#s.window),
			    ok;
			{cancel,S1} ->
			    {noreply, S1}
		    end;
	       true ->
		    {stop, ok, S}
	    end;

        #wx{id=?wxID_NEW, event=#wxCommand{type=command_menu_selected}} ->
	    ?dbg("NEW\n",[]),
	    _Pid = varp_wx:start(),
	    {noreply, S};

        #wx{id=?wxID_SAVE, event=#wxCommand{type=command_menu_selected}} ->
	    %% FIXME: handle file error !!!
	    ?dbg("SAVE\n",[]),
	    case save(S, 0) of
		{ok,S1} ->
		    {noreply, S1};
		{cancel,S1} ->
		    {noreply, S1}
	    end;

        #wx{id=?wxID_SAVEAS, event=#wxCommand{type=command_menu_selected}} ->
	    ?dbg("SAVEAS\n",[]),
	    Dialog = wxFileDialog:new(S#s.window,
				      [{message, "Save a copy"},
				       {style,?wxFD_SAVE bor ?wxFD_OVERWRITE_PROMPT},
				       {defaultDir,S#s.dir},
				       {wildCard,"*.varp;*.cnf;*.snf;*.txt"}]),
	    case wxFileDialog:showModal(Dialog) of
		?wxID_OK ->
		    Data = wxStyledTextCtrl:getText(S#s.formula),
		    BinData = unicode:characters_to_binary(Data),
		    Path = wxFileDialog:getPath(Dialog),
		    Dir = wxFileDialog:getDirectory(Dialog),
		    Filename = wxFileDialog:getFilename(Dialog),
		    wxFrame:setTitle(S#s.window, Filename),
		    file:write_file(Path, BinData),
		    wxMenuItem:enable(S#s.menu_save,[{enable,false}]),
		    wxDialog:destroy(Dialog),
		    wxStyledTextCtrl:connect(S#s.formula,?STCMOD),
		    {noreply, S#s { dir=Dir,
				    filename=Filename,
				    path = Path,
				    modified = false }};
		?wxID_CANCEL ->
		    wxDialog:destroy(Dialog),
		    {noreply, S}
	    end;

        #wx{id=?ID_EXPORT_CNF, event=#wxCommand{type=command_menu_selected}} ->
	    ?dbg("EXPORT_CNF\n",[]),
	    Dialog = wxFileDialog:new(S#s.window,
				      [{message, "Export CNF"},
				       {style,?wxFD_SAVE bor
					    ?wxFD_OVERWRITE_PROMPT},
				       {defaultDir,S#s.export_dir},
				       {wildCard,"*.cnf"}]),
	    case wxFileDialog:showModal(Dialog) of
		?wxID_OK ->
		    Path = wxFileDialog:getPath(Dialog),
		    Dir = wxFileDialog:getDirectory(Dialog),
		    File = add_extension(Path, ".cnf"),
		    S1 = export(cnf, File, S),
		    wxDialog:destroy(Dialog),
		    {noreply, S1#s { export_dir=Dir }};
		?wxID_CANCEL ->
		    wxDialog:destroy(Dialog),
		    {noreply, S}
	    end;

        #wx{id=?ID_EXPORT_SNF, event=#wxCommand{type=command_menu_selected}} ->
	    ?dbg("EXPORT_SNF\n",[]),
	    Dialog = wxFileDialog:new(S#s.window,
				      [{message, "Export SNF"},
				       {style,?wxFD_SAVE bor
					    ?wxFD_OVERWRITE_PROMPT},
				       {defaultDir,S#s.export_dir},
				       {wildCard,"*.snf"}]),
	    case wxFileDialog:showModal(Dialog) of
		?wxID_OK ->
		    Path = wxFileDialog:getPath(Dialog),
		    Dir = wxFileDialog:getDirectory(Dialog),
		    File = add_extension(Path, ".snf"),
		    S1 = export(snf, File, S),
		    wxDialog:destroy(Dialog),
		    {noreply, S1#s { export_dir=Dir }};
		?wxID_CANCEL ->
		    wxDialog:destroy(Dialog),
		    {noreply, S}
	    end;

        #wx{id=?wxID_OPEN, event=#wxCommand{type=command_menu_selected}} ->
	    ?dbg("OPEN\n",[]),
	    if S#s.modified ->
		    case save_before(S, "Save before open new") of
			{ok,S1} ->
			    case open_new(S1) of
				{ok,S2} -> {noreply, S2};
				{cancel,S2} -> {noreply, S2}
			    end;
			{cancel,S1} ->
			    {noreply, S1}
		    end;
	       true ->
		    case open_new(S) of
			{ok,S1} -> {noreply, S1};
			{cancel,S1} -> {noreply, S1}
		    end
	    end;

        #wx{id=?wxID_CUT,event=#wxCommand{type=command_menu_selected}} ->
	    case wxStyledTextCtrl:getSelection(S#s.formula) of
		{N,N} -> {noreply, S};
		_ ->
		    wxStyledTextCtrl:cut(S#s.formula),
		    {noreply, S}
	    end;

        #wx{id=?wxID_COPY,event=#wxCommand{type=command_menu_selected}} ->
	    case wxStyledTextCtrl:getSelection(S#s.formula) of
		{N,N} ->
		    case wxStyledTextCtrl:getSelection(S#s.model) of
			{K,K} -> {noreply, S};
			_ ->
			    wxStyledTextCtrl:copy(S#s.model),
			    {noreply,S}
		    end;
		_ ->
		    wxStyledTextCtrl:copy(S#s.formula),
		    {noreply,S}
	    end;

        #wx{id=?wxID_PASTE,event=#wxCommand{type=command_menu_selected}} ->
	    %% FIXME: check focus!
            wxStyledTextCtrl:paste(S#s.formula),
	    {noreply,S};

        #wx{id=?wxID_CLEAR,event=#wxCommand{type=command_menu_selected}} ->
	    case wxStyledTextCtrl:getSelection(S#s.formula) of
		{N,N} -> {noreply,S};
		{_N,_M} ->
		    wxStyledTextCtrl:clear(S#s.formula),
		    {noreply,S}
	    end;

        #wx{id=?wxID_SELECTALL,event=#wxCommand{type=command_menu_selected}} ->
            wxStyledTextCtrl:selectAll(S#s.formula),
	    {noreply,S};

        #wx{id=?wxID_ABOUT, event=#wxCommand{type=command_menu_selected}} ->
            dialog(?wxID_ABOUT, S#s.window),
	    {noreply,S};

        #wx{event=#wxSplitter{type=command_splitter_sash_pos_changed}} ->
	    %% not used yet
	    {noreply,S};

        #wx{obj=Obj,event=#wxStyledText{type=?STCMOD, text=""}} when
	      Obj =:= S#s.formula ->
	    {noreply,S};

        #wx{obj=Obj,event=#wxStyledText{type=?STCMOD}} when
	      Obj =:= S#s.formula, not S#s.modified ->
	    ?dbg("modified Event = ~p\n", [Event]),
	    Title = wxFrame:getTitle(S#s.window),
	    wxFrame:setTitle(S#s.window, [$*|Title]),
	    wxStyledTextCtrl:disconnect(S#s.formula, ?STCMOD),
	    wxMenuItem:enable(S#s.menu_save,[{enable,true}]),
	    {noreply,S#s { modified = true }};

        #wx{obj=Obj,event=#wxMouse{type=left_down}} when
	      Obj =:= S#s.formula ->
	    if S#s.error ->
		    hide_line(S#s.formula),
		    {noreply, S#s { error = false }};
	       true ->
		    {noreply, S}
	    end;

        #wx{obj=Obj,event=#wxKey{type=key_down}} when
	      Obj =:= S#s.formula ->
	    if S#s.error ->
		    hide_line(S#s.formula),
		    {noreply, S#s { error = false }};
	       true ->
		    {noreply, S}
	    end;

        _Msg = #wx{obj=Obj, event=#wxCommand{type=command_button_clicked}} ->
	    if S#s.satisfy =:= Obj ->
		    S1 = solve(satisfy, S),
		    {noreply, S1};
	       S#s.falsify =:= Obj ->
		    S1 = solve(falsify, S),
		    {noreply, S1};
	       S#s.settings =:= Obj ->
		    P = wxChoice:getSelection(S#s.config_profile),
		    wxNotebook:setSelection(S#s.config_notebook, P),
		    wxSplitterWindow:hide(S#s.splitter),
		    wxPanel:show(S#s.setting_panel),
		    wxWindow:layout(S#s.window),
		    {noreply, S};
	       S#s.setting_apply =:= Obj ->
		    P = wxNotebook:getSelection(S#s.config_notebook),
		    wxChoice:setSelection(S#s.config_profile, P),
		    wxPanel:hide(S#s.setting_panel),
		    wxSplitterWindow:show(S#s.splitter),
		    wxWindow:layout(S#s.window),
		    ValueMap = varp_wx_settings:get_values(
				 S#s.setting_widgets, S#s.setting_values),
		    profile_update(S#s.config_profile, ValueMap),
		    ok = varp_wx_settings:save(ValueMap),
		    {noreply, S#s { setting_values = ValueMap }};
	       S#s.setting_cancel =:= Obj ->
		    wxPanel:hide(S#s.setting_panel),
		    wxSplitterWindow:show(S#s.splitter),
		    wxWindow:layout(S#s.window),
		    %% restore values (fixme only if changed)
		    varp_wx_settings:set_values(S#s.setting_widgets,
						S#s.setting_values),
		    {noreply, S};
	       true ->
		    ?dbg("Got command_button_clicked ~p ~n", [_Msg]),
		    {noreply, S}
	    end;
        _Msg = #wx{} ->
            ?dbg("Got ~p ~n", [_Msg]),
	    {noreply, S}
    end.

open_new(S) ->
    Dialog = wxFileDialog:new(S#s.window,
			      [{message, "Open a file"},
			       {style, ?wxFD_OPEN},
			       {defaultDir,S#s.dir},
			       {wildCard,
				"*.varp;*.cnf;*.snf;*.txt"}]),
    case wxFileDialog:showModal(Dialog) of
	?wxID_OK ->
	    Path = wxFileDialog:getPath(Dialog),
	    case file:read_file(Path) of
		{ok,Bin} ->
		    wxStyledTextCtrl:disconnect(S#s.formula,?STCMOD),
		    %% clear model
		    wxStyledTextCtrl:setReadOnly(S#s.model, false),
		    wxStyledTextCtrl:clearAll(S#s.model),
		    wxStyledTextCtrl:setScrollWidth(S#s.model, 1),
		    wxStyledTextCtrl:setReadOnly(S#s.model, true),
		    %% load formula text
		    wxStyledTextCtrl:clearAll(S#s.formula),
		    wxStyledTextCtrl:setScrollWidth(S#s.formula, 1),
		    wxStyledTextCtrl:setTextRaw(S#s.formula,
						<<Bin/binary,0>>),
		    Dir = wxFileDialog:getDirectory(Dialog),
		    Filename = wxFileDialog:getFilename(Dialog),
		    wxFrame:setTitle(S#s.window, Filename),
		    wxStyledTextCtrl:connect(S#s.formula,?STCMOD),
		    wxMenuItem:enable(S#s.menu_save,[{enable,false}]),
		    wxDialog:destroy(Dialog),
		    {ok, S#s { dir=Dir,
			       filename=Filename,
			       path = Path,
			       modified = false }};
		{error,Reason} ->
		    wxDialog:destroy(Dialog),
		    Text = io_lib:format("file error: ~s ~p",
					 [Path,Reason]),
		    ok = wxFrame:setStatusText(S#s.window, Text),
		    {cancel, S}
	    end;
	?wxID_CANCEL ->
	    wxDialog:destroy(Dialog),
	    {cancel, S}
    end.


save_before(S, Message) ->
    Dialog = wxMessageDialog:new(S#s.window, Message,
				 [{style, ?wxYES bor ?wxNO bor ?wxCANCEL}]),
    case wxMessageDialog:showModal(Dialog) of
	?wxID_YES ->
	    wxDialog:destroy(Dialog),
	    save(S, ?wxFD_OVERWRITE_PROMPT);
	?wxID_NO ->
	    wxDialog:destroy(Dialog),
	    {ok,S};
	?wxID_CANCEL ->
	    wxDialog:destroy(Dialog),
	    {cancel,S}
    end.

save(S, Overwrite) ->
    if S#s.path =:= undefined ->
	    Dialog = wxFileDialog:new(S#s.window,
				      [{message,"Save file"},
				       {style, ?wxFD_SAVE bor Overwrite},
				       {defaultDir,S#s.dir},
				       {wildCard,
					"*.varp;*.cnf;*.snf;*.txt"}]),
	    case wxFileDialog:showModal(Dialog) of
		?wxID_OK ->
		    Data = wxStyledTextCtrl:getText(S#s.formula),
		    BinData = unicode:characters_to_binary(Data),
		    Path = wxFileDialog:getPath(Dialog),
		    Dir = wxFileDialog:getDirectory(Dialog),
		    Filename = wxFileDialog:getFilename(Dialog),
		    wxFrame:setTitle(S#s.window, Filename),
		    file:write_file(Path, BinData),
		    wxStyledTextCtrl:connect(S#s.formula,?STCMOD),
		    wxMenuItem:enable(S#s.menu_save,[{enable,false}]),
		    wxDialog:destroy(Dialog),
		    {ok,S#s { dir=Dir,
			      filename=Filename,
			      path = Path,
			      modified = false }};
		?wxID_CANCEL ->
		    wxDialog:destroy(Dialog),
		    {cancel, S}
	    end;
       true ->
	    Data = wxStyledTextCtrl:getText(S#s.formula),
	    BinData = unicode:characters_to_binary(Data),
	    file:write_file(S#s.path, BinData),
	    wxFrame:setTitle(S#s.window, S#s.filename),
	    wxStyledTextCtrl:connect(S#s.formula,?STCMOD),
	    wxMenuItem:enable(S#s.menu_save,[{enable,false}]),
	    {ok, S#s { modified = false}}
    end.

%% FIXME block interface while running
solve(Mode, S) ->
    Meta  = wxTextCtrl:getValue(S#s.meta),
    case varp:tokens(Meta) of
	{ok,Ts} ->
	    case parse_bindings(Ts) of
		{ok,L} ->
		    solve(Mode, S, L);
		{error,{_,Reason,Mess1}} ->
		    Err = io_lib:format("~w ~p\n",
					[Reason,Mess1]),
		    output_error(S, Err)
	    end;
	Error ->
	    Err = io_lib:format("~p", [Error]),
	    output_error(S, Err)
    end.

%% Update profile labels to the assigned names, use index
%% if not set
profile_update(Profile, Values) ->
    lists:foreach(
      fun(I) ->
	      case read_p([profile,I,name],Values,[]) of
		  [] ->
		      Name = integer_to_list(I),
		      wxChoice:setString(Profile,I-1,Name);
		  Name ->
		      wxChoice:setString(Profile,I-1,Name)
	      end
      end, lists:seq(1, 10)).

profile_number(S) ->
    wxChoice:getSelection(S#s.config_profile) + 1.

solve(Mode, S, Bound) ->
    I = profile_number(S),
    Pfx = [profile,I,options],

    Max       = wxSpinCtrl:getValue(S#s.config_max_models),
    Timeout   = case wxSpinCtrl:getValue(S#s.config_timeout) of
		    0 -> infinity;
		    T -> T
		end,
    Saturate = read_saturate_params(S,I),
    Method = read_param([profile,I],method,S,backjump),
    Order_1 = read_param(Pfx,[order,key1,sort],S,degree),
    Ascend_1   = read_param(Pfx,[order,key1,dir],S,false),
    Order_2 = read_param(Pfx,[order,key2,sort],S,degree),
    Ascend_2   = read_param(Pfx,[order,key2,dir],S,false),
    Assoc   = read_param(Pfx,[varp,assoc],S,none),
    QType   = read_param(Pfx,[varp,qtype],S,recursive),
    %% _EdgeList = true,
    ?dbg("max  = ~p\n", [Max]),
    ?dbg("saturate = ~w\n", [Saturate]),
    ?dbg("method = ~w\n", [Method]),
    ?dbg("order = ~w\n", [[{Order_1,Ascend_1},{Order_2,Ascend_2}]]),
    ?dbg("assoc = ~w\n", [Assoc]),
    ?dbg("qtype = ~w\n", [QType]),
    ?dbg("timeout = ~w\n", [Timeout]),

    Formula = wxStyledTextCtrl:getText(S#s.formula),
    Meta = maps:from_list(Bound),
    Partial = (Method =:= none) 
	orelse 
	  ((Method =:= backjump) 
	   andalso is_number(Timeout) 
	   andalso (Timeout > 0)),
    case parse(Formula, Meta) of
	{ok,{Sections,Form}} ->
	    Options = [{method,count},{print,true},{timeout,Timeout},
		       {assoc,Assoc},{qtype,QType},{xref,true},
		       {partial,Partial}
		      ],
	    GOpts = varp:load_option_list(Options),
	    GOpts1 = varp:section_opts(Sections, GOpts),

	    Order =
		if Order_1 =:= undefined, Order_2 =:= undefined ->
			case maps:find(order, GOpts1) of
			    {ok, FileOrder} ->
				[{order, FileOrder}];
			    _ ->
				[]
			end;
		   Order_2 =:= undefined ->
			[{order,[{sort,[order(Ascend_1,Order_1)]}]}];
		   Order_1 =:= undefined ->
			[{order,[{sort,[order(Ascend_2,Order_2)]}]}];
		   true -> [{order,[{sort,[order(Ascend_1,Order_1),
					   order(Ascend_2,Order_2)]}]}]
		end,
	    Do =
		[{wx,[{nbound,S#s.config_nbound},
		      {window,S#s.window},
		      {env, S#s.wx_env}]},
		 {Mode,[]}] ++
		Order ++
		case lists:keyfind(level,1,Saturate) of
		    {level,0} -> [];
		    _ ->
			[{saturate, Saturate}]
		end ++
		case Method of
		    backjump ->
			BjParams = read_backjump_params(S, I),
			[{backjump, [{max,Max}]++BjParams}];
		    backtrack ->
			[{backtrack,[{max,Max}]}];
		    none ->
			[]
		end,

	    GDo = varp:parse_do(Do),

	    GOpts2 = GOpts1#{ meta => Meta,
			      output => [{?MODULE,output_model,[S]}] },
	    output_clear(S),

	    ok = wxFrame:setStatusText(S#s.window, "ok",[]),

	    wxButton:disable(S#s.satisfy),
	    wxButton:disable(S#s.falsify),
	    wxButton:enable(S#s.cancel),
	    wxButton:disable(S#s.settings),

	    try varp:do_run(GDo,Form,GOpts2) of
		{?INCONSISTENT,_,_Bs} ->
		    if Mode =:= falsify ->
			    output_text(S, "VALID\n");
		       true ->
			    output_text(S, "UNSATISFIABLE\n")
		    end;
		{?DONE, _, _Bs} ->
		    S;
		{?CONTINUE, N, _Bs} when is_integer(N) ->
		    if N =:= Max ->
			    output_text(S, "...\n");
		       true ->
			    S
		    end;
		{?CONTINUE, [], _Bs} ->
		    S;
		{?TIMEOUT,_,_} ->
		    output_text(S, "TIMEOUT\n");
		{?CANCEL,_,_} ->
		    output_text(S, "USER ABORT\n");
		{?ERROR,_,_} ->
		    output_text(S, "ERROR\n");
		Res ->
		    output_error(S, io_lib:format("unexpected ~p\n", [Res]))
	    catch
		?EXCEPTION(error,Reason,Trace) ->
		    S1 = output_error(S, varp:format_error(Reason)),
		    io:format("exception:~w\n~p\n", [Reason,?GET_STACK(Trace)]),
		    S1
	    after
		wxButton:enable(S#s.satisfy),
		wxButton:enable(S#s.falsify),
		wxButton:disable(S#s.cancel),
		wxButton:enable(S#s.settings),

		call(get(mon_proc), flush),
		call(get(mon_proc), stop)
	    end;

	{error, {Ln,Mod,Message}} when is_integer(Ln), is_atom(Mod) ->
	    show_line(S#s.formula, Ln),
	    mark_line(S#s.formula, Ln),
	    wxStyledTextCtrl:refresh(S#s.formula),
	    Text = (catch apply(Mod, format_error, [Message])),
	    S1 = output_error(S, Text),
	    S1#s { error = true };

	{error, {Ln,Mod,Message}, _EndLn} when is_integer(Ln), is_atom(Mod) ->
	    show_line(S#s.formula, Ln),
	    mark_line(S#s.formula, Ln),
	    wxStyledTextCtrl:refresh(S#s.formula),
	    Text = (catch apply(Mod, format_error, [Message])),
	    S1 = output_error(S, Text),
	    S1#s { error = true };

	{error, Message} ->
	    output_error(S, varp:format_error(Message))
    end.

order(DoAscend, Ord) ->
    Dir = case DoAscend of
	      descend -> -1;  %% backwards compatible values
	      ascend  ->  1;
	      0       -> -1;
	      false   -> -1;
	      1       -> 1;
	      true    -> 1;
	      undefined -> 0
	  end,
    if Dir =:= 0 ->  %% default direction (is decend)
	    Ord;
       Dir < 0 ->
	    case Ord of
		degree    -> '-degree';
		rank      -> '-rank';
		activity  -> '-degree';
		user      -> '-user';
		random    -> '-random';
		identity  -> '-identity';
		undefined -> undefined
	    end;
       Dir > 0 ->
	    case Ord of
		degree    -> '+degree';
		rank      -> '+rank';
		activity  -> '+degree';
		user      -> '+user';
		random    -> '+random';
		identity  -> '+identity';
		undefined -> undefined
	    end
    end.

%% add inc_learned_factor - no units found for T seconds
read_backjump_params(S,I) ->
    [
     %% {display,    true},
     {minimize,           read_param(?BJK(I,minimize), S, none)},
     {stumble,            read_param(?BJK(I,stumble), S, 0)},
     {olle,               read_param(?BJK(I,olle), S, 0)},
     {stumble_olle,       read_param(?BJK(I,stumble_olle), S, false)},
     {max_conflicts,      read_param(?BJK(I,max_conflicts), S, 1) },
     {max_learned,        read_param(?BJK(I,max_learned), S, 0) },
     {max_learned_factor, read_param(?BJK(I,max_learned_factor), S, 0) },
     {max_learned_inc,    read_param(?BJK(I,max_learned_inc), S, 0)},
     {keep_factor,        read_param(?BJK(I,keep_factor), S, 0.5) },
     {min_keep_clauses,   read_param(?BJK(I,min_keep_clauses), S, 0)},
     {restart_counter,    read_param(?BJK(I,restart_counter), S, 0) },
     {restart_interval,   read_param(?BJK(I,restart_interval), S, 0)},
     {bump,               read_param(?BJK(I,bump), S, 1) },
     {reorder, ?REORDER_NONE}
    ].

read_saturate_params(S,I) ->
    [{level, wxSpinCtrl:getValue(S#s.config_saturate)},
     {q, read_param(?SAT(I,q), S, 0)},
     {f, read_param(?SAT(I,f), S, 0)},
     {r, read_param(?SAT(I,r), S, 0)},
     {laps, read_param(?SAT(I,laps), S, 0)},
     {threshold, read_param(?SAT(I,threshold), S, 0)}
    ].

read_param(Pfx, Key, S, Default) when is_atom(Key) ->
    read_param(Pfx++[Key], S, Default);
read_param(Pfx, Key, S, Default) when is_list(Key) ->
    read_param(Pfx++Key, S, Default).

read_param(Key, #s{ setting_values=ValueMap}, Default) when is_list(Key) ->
    read_p(Key, ValueMap, Default).

read_p(Key, ValueMap, Default) when is_list(Key), is_map(ValueMap) ->
    maps:get(Key, ValueMap, Default).

%% add extension only if there no extension to the name
add_extension(Path, Ext) ->
    case filename:extension(Path) of
	"" -> Path ++ Ext;
	_ -> Path
    end.

export(Type, File, S) ->
    Meta  = wxTextCtrl:getValue(S#s.meta),
    case varp:tokens(Meta) of
	{ok,Ts} ->
	    case parse_bindings(Ts) of
		{ok,L} ->
		    export(Type, File, S, L);
		{error,{_,Reason,Mess1}} ->
		    Err = io_lib:format("~w ~p\n",
					[Reason,Mess1]),
		    output_error(S, Err)
	    end;
	Error ->
	    Err = io_lib:format("~p", [Error]),
	    output_error(S, Err)
    end.

-define(VKEY(I,Name), [profile,(I),options,varp,(Name)]).

export(Type, File, S, Bound) ->
    I = profile_number(S),
    Saturate = read_saturate_params(S,I), %% FIXME: may depend on ORDER!!!
    Assoc     = read_param(?VKEY(I,assoc),S,none),
    Formula = wxStyledTextCtrl:getText(S#s.formula),
    Meta = maps:from_list(Bound),
    case parse(Formula, Meta) of
	{ok,{Sections,Form}} ->
	    Options = [{assoc,Assoc},{phase,true},{use_phase,true}],
	    GOpts = varp:load_option_list(Options),
	    GOpts1 = varp:section_opts(Sections, GOpts),
	    Do =
		[{satisfy,[]}] ++
		case lists:keyfind(level,1,Saturate) of
		    {level,0} -> [];
		    _ -> [{saturate,Saturate}]
		end ++
		[{cnf, [{type,Type},{file,File},{symbols,true}]}],

	    GDo = varp:parse_do(Do),

	    GOpts2 = GOpts1#{ meta => Meta,
			      output => [{?MODULE,output_model,[S]}] },
	    output_clear(S),
	    ok = wxFrame:setStatusText(S#s.window, "export ok",[]),

	    try varp:do_run(GDo,Form,GOpts2) of
		{?CONTINUE, [], _Bs} ->
		    S;
		{?ERROR,_,_} ->
		    output_text(S, "ERROR\n");
		Res ->
		    output_error(S, io_lib:format("unexpected ~p\n", [Res]))
	    catch
		?EXCEPTION(error,Reason,Trace) ->
		    S1 = output_error(S, varp:format_error(Reason)),
		    io:format("Stack: ~p\n", [?GET_STACK(Trace)]),
		    S1
	    end;

	{error, {Ln,Mod,Message}} when is_integer(Ln), is_atom(Mod) ->
	    show_line(S#s.formula, Ln),
	    mark_line(S#s.formula, Ln),
	    wxStyledTextCtrl:refresh(S#s.formula),
	    Text = (catch apply(Mod, format_error, [Message])),
	    S1 = output_error(S, Text),
	    S1#s { error = true };

	{error, {Ln,Mod,Message}, _EndLn} when is_integer(Ln), is_atom(Mod) ->
	    show_line(S#s.formula, Ln),
	    mark_line(S#s.formula, Ln),
	    wxStyledTextCtrl:refresh(S#s.formula),
	    Text = (catch apply(Mod, format_error, [Message])),
	    S1 = output_error(S, Text),
	    S1#s { error = true };

	{error, Message} ->
	    output_error(S, io_lib:format("~p\n", [Message]))
    end.

mark_line(Stc, Line) ->
    wxStyledTextCtrl:setCaretLineBackground(Stc, {255, 50, 50}),
    Start = wxStyledTextCtrl:positionFromLine(Stc, Line-1),
    wxStyledTextCtrl:setCurrentPos(Stc, Start),
    wxStyledTextCtrl:setSelection(Stc, Start, Start).

show_line(Stc, Line) ->
    wxStyledTextCtrl:scrollToLine(Stc, Line-1),
    wxStyledTextCtrl:setCaretLineVisible(Stc, true),
    wxStyledTextCtrl:setFocus(Stc).

hide_line(Stc) ->
    wxStyledTextCtrl:setCaretLineVisible(Stc, false).

output_error(S, Text) ->
    output_clear(S),
    ok = wxFrame:setStatusText(S#s.window, "Error",[]),
    output_text(S, ["ERROR: ", Text]).

output_text(S, Text) ->
    wxStyledTextCtrl:setReadOnly(S#s.model, false),
    wxStyledTextCtrl:addText(S#s.model, Text),
    wxStyledTextCtrl:setReadOnly(S#s.model, true),
    S.

output_clear(S) ->
    wxStyledTextCtrl:setReadOnly(S#s.model, false),
    wxStyledTextCtrl:clearAll(S#s.model),
    wxStyledTextCtrl:setReadOnly(S#s.model, true).

%% varp output function, first two arguments are fixed, reset
%% is passed in the output parameter list
output_model(_Fd, Partial, Model, S) ->
    wxStyledTextCtrl:setReadOnly(S#s.model, false),
    if Partial ->
	    wxStyledTextCtrl:addText(S#s.model, ["PARTIAL\n"]);
       true ->
	    ok
    end,
    List = [ varp_formula:format_binding(B) ||
	       B <- varp_formula:filter_bindings(Model),
	       Partial orelse (element(2,B) =/= false) ],
    Chars = lists:join(",", List),
    wxStyledTextCtrl:addText(S#s.model, [Chars,"\n"]),
    wxStyledTextCtrl:setReadOnly(S#s.model, true),
    ok.

parse_bindings(Ts) ->
    parse_bindings_(Ts, []).

parse_bindings_([{symbol,_Ln1,Name},{'=',_Ln2},{decnum,_Ln3,Int}|Ts],
		Acc) ->
    parse_bindings_(Ts, [{Name, list_to_integer(Int,10)}|Acc]);
parse_bindings_([{symbol,_Ln1,Name},{'=',_Ln2},{hexnum,_Ln3,Int}|Ts],
		Acc) ->
    parse_bindings_(Ts, [{Name, list_to_integer(Int,16)}|Acc]);
parse_bindings_([{symbol,_Ln1,Name},{'=',_Ln2},{octnum,_Ln3,Int}|Ts],
		Acc) ->
    parse_bindings_(Ts, [{Name, list_to_integer(Int,8)}|Acc]);
parse_bindings_([{symbol,_Ln1,Name},{'=',_Ln2},{binnum,_Ln3,Int}|Ts],
		Acc) ->
    parse_bindings_(Ts, [{Name, list_to_integer(Int,2)}|Acc]);
parse_bindings_([{symbol,_Ln1,Name},{'=',_Ln2},{string,_Ln3,Str}|Ts],
		Acc) ->
    parse_bindings_(Ts, [{Name, Str}|Acc]);
parse_bindings_([{symbol,_Ln1,Name},{'=',_Ln2},{symbol,_Ln3,Str}|Ts],
		Acc) ->
    %% lookup value? is this done later?
    parse_bindings_(Ts, [{Name,Str}|Acc]);
parse_bindings_([{',',_ln}|Ts], Acc) ->
    parse_bindings_(Ts, Acc);
parse_bindings_([{';',_ln}|Ts], Acc) ->
    parse_bindings_(Ts, Acc);
parse_bindings_([T={_,Ln}|_Ts], _Acc) ->
    {error, {Ln, unexpected_token, T}};
parse_bindings_([T={_,Ln,_}|_Ts], _Acc) ->
    {error, {Ln, unexpected_token, T}};
parse_bindings_([], Acc) ->
    {ok,lists:reverse(Acc)}.

parse(String, Meta) ->
    ICase = false,  %% Fixme: icase option
    Scan = if ICase -> varp_scani;
	      true -> varp_scan
	   end,
    case varp_dimacs:detect_data(String) of
	false ->
	    Scan:init(varp:remove_comments(String)),
	    case varp_parse:parse_and_scan({Scan, one_token, []}) of
		{ok,{Sections,_Assignments,Formula}} ->
		    GOpts = #{ meta => Meta },
		    try varp:split_sections(Sections,GOpts) of
			{ok, SectionMap} ->
			    {ok,{SectionMap,Formula}};
			Error ->
			    Error
		    catch
			error:Reason ->
			    {error,Reason}
		    end;
		Error -> Error
	    end;
	{ok,_CnfType} ->
	    parse_dimacs(String)
    end.

parse_dimacs(String) ->
    Bin = list_to_binary(String), %% utf?
    case varp_dimacs:parse(Bin) of
	Form={cnf,{_Var,_Clause,SectionMap,_Cs}} ->
	    {ok,{SectionMap,Form}};
	Form={snf,{_Var,_Clause,SectionMap,_Cs}} ->
	    {ok,{SectionMap,Form}};
	Error ->
	    Error
    end.

dialog(?wxID_ABOUT,  Frame) ->
    Str = string:join(["Varp ", version(),
		       " is a propositional theorem prover\n",
                       "running under ",
		       wx_misc:getOsDescription(),
                       "."],
                      ""),
    MD = wxMessageDialog:new(Frame,
                             Str,
                             [{style, ?wxOK bor ?wxICON_INFORMATION},
                              {caption, "About varp"}]),

    wxDialog:showModal(MD),
    wxDialog:destroy(MD).


keyWords() ->
    L = ["EQ", "NEQ", "GT", "GTE", "LT", "LTE", "NONE", "ONE",
	 "PARITY", "ODD", "EVEN",
	 "symbol", "true", "false", "define", "declare", "literals",
	 "assert", "input", "output", "order", "rank", "degree",
	 "random", "identity",
	 "and", "or", "xor", "not",
	 "implies", "imp",
	 "equivalent", "equ",
	 "A", "ALL",
	 "E", "ANY",
	 "SUM", "PROD"],
    lists:flatten([K ++ " " || K <- L] ++ [0]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  varp plugin for monitoring assignments, updating statistics time etc
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% built in plugin to monitor variables
options() ->
    [
     #{ key => nbound,
	spec => term,
	default => undefined,
	description => "wxGauge setting % of bound variables."
      },
     #{ key => window,
	spec => term,
	default => undefined,
	description => "top wxFrame container."
      },
    #{ key => env,
       spec => term,
       default => undefined,
       description => "wx environment passed to plugin, use wx:set_env."
     }
    ].

run(Bs, Param) ->
    SELF = self(),
    Info = [atom,variable,
	    number_of_variables,
	    number_of_bound_variables,
	    number_of_subst_variables,
	    number_of_clauses,
	    number_of_dead_clauses,
	    number_of_conflicts
	   ],
    Ref = make_ref(),
    {Pid,Mon} =
	spawn_monitor(
	  fun() ->
		  ?dbg("varp_wx monitor ~p started\n", [self()]),
		  ok = varp_nif:subscribe(Bs#bs.vp, Info),
		  Mon = monitor(process, SELF),
		  SELF ! {ack,Ref},
		  wx:set_env(maps:get(env, Param)),
		  T0 = erlang:monotonic_time(),
		  mon_loop(Bs, Param, Mon, T0, get_info(Bs))
	  end),
    receive
	{ack,Ref} ->
	    erlang:demonitor(Mon);
	{'DOWN', Mon, process, Pid, _Reason} ->
	    ok
    after 3000 ->
	    ?dbg("need to wait longer?\n",[]),
	    timeout
    end,
    put(mon_proc, Pid),  %% must be killed after each run!
    {?CONTINUE,[],Bs}.

mon_loop(Bs,Param,Mon,StartTime,PrevInfo) ->
    receive
	{'DOWN', Mon, process, _Pid, _Reason} ->
	    done;
	{call, From, flush} ->
	    Info = get_info(Bs),
	    update_info(Param,StartTime,Info),
	    response(From, ok),
	    mon_loop(Bs,Param,Mon,StartTime,Info);
	{call, From, stop} ->
	    update_info(Param,StartTime,PrevInfo),
	    response(From, ok);
	{varp, {_X,_Y}, Info} ->
	    ?dbg("varp_wx monitor: substitut (~w=>~w) ~s => ~s,info=~w\n",
		 [_Y,_X, varp_formula:format_lit(Bs,_Y),
		  varp_formula:format_lit(Bs,_X),Info]),
	    Info1 = mon_loop_collect(Info),
	    Info2 = merge_info(Info1, PrevInfo),
	    update_info(Param,StartTime,Info2),
	    mon_loop(Bs,Param,Mon,StartTime,Info2);
	{varp, _X, Info} ->
	    ?dbg("varp_wx monitor: permanent (~w=1) ~s = ~w,info=~w\n",
		 [_X,varp_formula:format_lit(Bs,_X), 1, Info]),
	    Info1 = mon_loop_collect(Info),
	    Info2 = merge_info(Info1, PrevInfo),
	    update_info(Param,StartTime,Info2),
	    mon_loop(Bs,Param,Mon,StartTime,Info2);
	Other ->
	    io:format("varp_wx monitor: got ~p\n", [Other]),
	    mon_loop(Bs,Param,Mon,StartTime,PrevInfo)
    after 1000 ->
	    Info1 = get_info(Bs),
	    Info2 = merge_get_info(Info1, PrevInfo),
	    update_info(Param,StartTime,Info2),
	    mon_loop(Bs,Param,Mon,StartTime,Info2)
    end.

mon_loop_collect(Info) ->
    receive
	{varp, {_X,_Y}, Info1} ->
	    mon_loop_collect(Info1);
	{varp, _X, Info1} ->
	    mon_loop_collect(Info1)
    after 1 ->
	    Info
    end.

update_info(#{nbound:=NBound,window:=Window},StartTime,
	    #{number_of_variables:=NV,
	      number_of_bound_variables:=NB,
	      number_of_subst_variables:=NS,
	      number_of_clauses:=NC,
	      number_of_dead_clauses:=ND,
	      number_of_bcps:=NE,
	      max_level := XL,
	      min_level := IL,
	      number_of_conflicts := CF
	     }) ->
    CurrentTime = erlang:monotonic_time(),
    Time = erlang:convert_time_unit(CurrentTime - StartTime,
				    native, millisecond),
    NBS = [integer_to_list(NB),"[/",integer_to_list(NS),"]"],
    MIMA = [integer_to_list(XL),"[/",integer_to_list(IL),"]"],
    Status = io_lib:format(
	       "#Var: ~-8w #Bound: ~-16s #Clauses: ~-8w"
	       "#Dead: ~-8w #Bcp: ~-10w Depth: ~-9s #Confl: ~-10w Time: ~s",
	       [NV, NBS, NC, ND, NE, MIMA, CF, format_time(Time)]),
    wxGauge:setValue(NBound, trunc(100*(NB/max(1,NV)))),
    wxFrame:setStatusText(Window, Status,[]).

format_time(Ms) ->
    S0 = Ms div 1000,
    S = S0 rem 60,
    F = Ms rem 1000,  %% decimal fraction 3 digits
    %% F = round(((Ms rem 1000)/1000)*100),  decimal fraction 2digits
    if S0 >= 60 ->
	    M0 = S0 div 60,
	    M = M0 rem 60,
	    if M0 >= 60 ->
		    H = M0 div 60,
		    if H >= 24 ->
			    D = H div 24,
			    [integer_to_list(D),"d ",
			     f2i(H),$:,f2i(M),$:,f2i(S),$.,f3i(F)];
		       true ->
			    [f2i(H),$:,f2i(M),$:,f2i(S),$.,f3i(F)]
		    end;
	       true ->
		    [f2i(M),$:,f2i(S),$.,f3i(F)]
	    end;
       true ->
	    [f2i(S),$.,f3i(F)]
    end.

f3i(N) when N >= 0, N < 1000 ->
    tl(integer_to_list(1000 + N)).

%% format N as two digits
f2i(N) when N >= 0, N < 100 ->
    tl(integer_to_list(100 + N)).

merge_get_info(Info1, Info2) ->
    minfo([number_of_clauses,
	   number_of_dead_clauses,
	   number_of_bcps,
	   max_level,
	   min_level,
	   number_of_conflicts
	  ],
	  Info1, Info2).

merge_info(Info1, Info2) ->
    minfo([number_of_bound_variables,
	   number_of_subst_variables,
	   number_of_clauses,
	   number_of_dead_clauses,
	   number_of_bcps,
	   max_level,
	   min_level,
	   number_of_conflicts
	  ],
	  Info1, Info2).

minfo([Key|Ks], Src, Dst) ->
    case maps:get(Key, Src, undefined) of
	undefined -> minfo(Ks, Src, Dst);
	Value -> minfo(Ks, Src, maps:put(Key, Value, Dst))
    end;
minfo([], _Src, Dst) ->
    Dst.
	
get_info(Bs) ->
    #{ number_of_variables =>
	   varp_nif:getstat(Bs#bs.vp, number_of_variables),
       number_of_bound_variables => 
	   varp_nif:getstat(Bs#bs.vp, number_of_bound_variables),
       number_of_subst_variables => 
	   varp_nif:getstat(Bs#bs.vp, number_of_subst_variables),
       number_of_clauses =>
	   varp_nif:getstat(Bs#bs.vp, number_of_clauses),
       number_of_dead_clauses =>
	   varp_nif:getstat(Bs#bs.vp, number_of_dead_clauses),
       number_of_bcps =>
	   varp_nif:getstat(Bs#bs.vp, number_of_bcps),
       max_level =>
	   varp_nif:getstat(Bs#bs.vp,max_level),
       min_level =>
	   varp_nif:getstat(Bs#bs.vp,min_level),
       number_of_conflicts =>
	   varp_nif:getstat(Bs#bs.vp,number_of_conflicts)
     }.
       
call(undefined, _Request) ->
    noproc;
call(Pid, Request) ->
    Ref = erlang:monitor(process, Pid),
    Pid ! {call, {Ref,self()}, Request},
    receive
	{response,Ref,Response} ->
	    erlang:demonitor(Ref,[flush]),
	    Response;
	{'DOWN', Ref, process, Pid, _Reason} ->
	    down
    after 10000 ->
	    erlang:demonitor(Ref),
	    io:format("call failes?\n"),
	    timeout
    end.

response({Ref,Pid}, Response) ->
    Pid ! {response,Ref,Response}.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  varp wx window register
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

register_process() ->
    varp_wx_reg ! {register, self()}.

start_win_reg() ->
    STARTER = self(),
    {Pid,Mon} = spawn_monitor(
		  fun() ->
			  try register(varp_wx_reg, self()) of
			      true ->
				  STARTER ! {self(), ok},
				  varp_wx_reg_loop([])
			  catch
			      error:_ ->
				  STARTER ! {self(), already_started}
			  end
		  end),
    receive
	{'DOWN', Mon, process, Pid, Reason} ->
	    {error,Reason};
	{Pid, Message} ->
	    erlang:demonitor(Mon, [flush]),
	    Message
    end.

varp_wx_reg_loop(Ws) ->
    receive
	{register, Pid} ->
	    Mon = erlang:monitor(process, Pid),
	    varp_wx_reg_loop([{Mon,Pid}|Ws]);
	{'DOWN', Mon, process, _Pid, _Reason} ->
	    case lists:keytake(Mon, 1, Ws) of
		{value,_,[]} ->
		    erlang:halt(0);
		{value,_,Ws1} ->
		    varp_wx_reg_loop(Ws1);
		false ->
		    varp_wx_reg_loop(Ws)
	    end;
	Mesg ->
	    io:format("varp_wx_reg_loop: got ~w\n", [Mesg]),
	    varp_wx_reg_loop(Ws)
    end.
