%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    wx GUI for varp
%%% @end
%%% Created : 15 Sep 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_wx).

-include_lib("wx/include/wx.hrl").


-export([start/0]).
-export([main_loop/1]).

-export([output_model/3]).  %% varp callback

%% warp_wx is also a plugin (monitor assignment etc)
-export([options/0, run/2]).

%% debug export
-export([format_time/1]).

%% -define(DEBUG, true).
-include("varp.hrl").

-define(STCMOD, stc_modified).

-define(ID_EXPORT_CNF, 100).
-define(ID_EXPORT_SNF, 101).


-record(s,
	{
	 window,
	 meta,
	 formula,
	 modified = false, %% formula modified
	 error    = false, %% error is marked
	 model,
	 satisfy,
	 falsify,
	 cancel,
	 dir = "",
	 export_dir = "",
	 filename = undefined,
	 path = undefined,
	 wx_env,            %% environment passed to plugin 
	 %% menus
	 menu_save,         %% wxMenu
	 %% config
	 config_max_models, %% wxSpinCtrl
	 config_timeout,    %% wxSpinCtrl
	 config_saturate,   %% wxSpinCtrl (saturate=1 or none=0)
	 config_backtrack,  %% wxRadioBox (backtrack|backjump|none)
	 config_order,      %% wxRadioBox (-degree|-rank|eval|random|none)
	 config_assoc,      %% wxRadioBox (left|right|balanced|none)
	 config_nbound      %% wxGauge
	}).

version() ->
    {ok,Vsn} = application:get_key(varp, vsn),
    Vsn.

start() ->
    application:start(varp),
    application:load(wx),
    start_win_reg(),
    spawn(
      fun() ->
	      Wx = wx:new(),
	      %% try wx:batch(fun() -> create_window(Wx) end) of
	      try create_window(Wx) of
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


create_window(Wx) ->
    Window = wxFrame:new(Wx, -1, "Varp", [{size, {800,600}}]),

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

    %% Create varp GUI
    %%  +-----------------------------+
    %%  |  Meta (input)               |
    %%  +-----------------------------+
    %%  |  Formula (input)            |
    %%  |                             |
    %%  |                             |
    %%  |                             |
    %%  +-----------------------------+
    %%  +-----------------------------+
    %%  | |Satisfy| |Falsify| |Cancel |
    %%  |  Config ...                 |
    %%  +-----------------------------+
    %%  |  Model (output)             |
    %%  |                             |
    %%  +-----------------------------+
    %%
    %%  Config = spin-max-model, spin-timeout, backjump/backtrack backjump ...
    %%  +-----+--------+
    %%  | max | timeout|
    %%  +-----+--------+

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
    Meta = wxTextCtrl:new(Win1, 1, [{value, ""},
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
    Run = wxStaticBoxSizer:new(?wxHORIZONTAL,Win2,[{label, "run"}]),
    Satisfy = wxButton:new(Win2, 10, [{label,"Satisfy"}]),
    wxButton:connect(Satisfy, command_button_clicked),
    wxButton:enable(Satisfy),

    Falsify = wxButton:new(Win2, 11, [{label,"Falsify"}]),
    wxButton:connect(Falsify, command_button_clicked),
    wxButton:enable(Falsify),

    Cancel = wxButton:new(Win2, 12, [{label,"Cancel"}]),
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
    MaxBox = wxStaticBoxSizer:new(?wxVERTICAL,Win2,[{label, "max"}]),
    MaxModels = wxSpinCtrl:new(Win2, []),
    wxSpinCtrl:setRange(MaxModels, 1, 1000),
    wxSizer:add(MaxBox, MaxModels),

    TimeBox = wxStaticBoxSizer:new(?wxVERTICAL,Win2,[{label,"timeout"}]),
    Timeout = wxSpinCtrl:new(Win2, []),
    wxSpinCtrl:setRange(Timeout, 0, 100000),
    wxSizer:add(TimeBox, Timeout),

    SaturateBox = wxStaticBoxSizer:new(?wxVERTICAL,Win2,[{label,"saturate"}]),
    Saturate = wxSpinCtrl:new(Win2, []),
    wxSpinCtrl:setRange(Saturate, 0, 3),
    wxSizer:add(SaturateBox, Saturate),

    Backtrack = wxRadioBox:new(Win2, 21, "backtrack",
			       ?wxDefaultPosition,
			       ?wxDefaultSize,
			       ["backjump","backtrack","none"],
			       [{majorDim, 1}, {style, ?wxVERTICAL}]),

    Order = wxRadioBox:new(Win2, 22, "order",
			   ?wxDefaultPosition,
			   ?wxDefaultSize,
			   ["-deg", "-rank", "-usr", "rnd", "none"],
			   [{majorDim, 1},{style,  ?wxVERTICAL}]),

    Assoc = wxRadioBox:new(Win2, 23, "assoc",
			   ?wxDefaultPosition,
			   ?wxDefaultSize,
			   ["left", "right", "balanced", "none"],
			   [{majorDim, 1},{style,  ?wxVERTICAL}]),

    NBound = wxGauge:new(Win2, 31, 100, [{size,{800,10}},
					 {style, 
					  ?wxGA_HORIZONTAL+?wxGA_SMOOTH}]),

    Config = wxBoxSizer:new(?wxVERTICAL),
    Config1 = wxBoxSizer:new(?wxHORIZONTAL),
    Config2 = wxBoxSizer:new(?wxHORIZONTAL),
    wxSizer:add(Config, Config1, []),
    wxSizer:add(Config, Config2, []),
    wxSizer:add(Config, NBound, []),
    wxSizer:add(Config1, Run, []),
    wxSizer:add(Config1, MaxBox, []),
    wxSizer:add(Config1, TimeBox, []),
    wxSizer:add(Config1, SaturateBox, []),    
    wxSizer:add(Config2, Backtrack, []),
    wxSizer:add(Config2, Order, []),
    wxSizer:add(Config2, Assoc, []),

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
    wxFrame:setSizer(Window, MainSizer),

    wxFrame:setTitle(Window, "Untitled"),

    {ok, DefaultDir} = file:get_cwd(), %% fixme: save dir?
    #s { window = Window, 
	 meta = Meta,
	 formula = Formula,
	 model = Model,
	 falsify = Falsify,
	 satisfy = Satisfy,
	 cancel = Cancel,
	 filename = undefined,
	 path = undefined,
	 dir = DefaultDir,
	 config_max_models = MaxModels,
	 config_timeout    = Timeout,
	 config_saturate   = Saturate,
	 config_backtrack  = Backtrack,
	 config_order      = Order,
	 config_assoc      = Assoc,
	 config_nbound     = NBound,
	 wx_env            = wx:get_env(),
	 menu_save         = SaveMenuItem
       }.

main_loop(S) ->
    receive
	Event when is_record(Event, wx) ->
	    try handle_event(Event, S) of
		{noreply, S1} ->
		    ?MODULE:main_loop(S1);
		{stop, Reason, _S1} ->
		    Reason
	    catch
		?EXCEPTION(error,Reason,Trace) ->
		    io:format("error:~w\n~p\n", [Reason,?GET_STACK(Trace)])
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
    case varp_scan:string(Meta) of
	{ok,Ts,_Ln} ->
	    case parse_bindings(Ts) of
		{ok,L} -> 
		    solve(Mode, S, L);
		{error,{_Ln,Reason,Mess1}} ->
		    Err = io_lib:format("~w ~p\n", 
					[Reason,Mess1]),
		    output_error(S, Err)
	    end;
	Error ->
	    Err = io_lib:format("~p", [Error]),
	    output_error(S, Err)
    end.

solve(Mode, S, Bound) ->
    Max       = wxSpinCtrl:getValue(S#s.config_max_models),
    Timeout   = case wxSpinCtrl:getValue(S#s.config_timeout) of
		    0 -> infinity;
		    T -> T
		end,
    Saturate  = wxSpinCtrl:getValue(S#s.config_saturate),
    Backtrack = wxRadioBox:getSelection(S#s.config_backtrack),
    Order     = wxRadioBox:getSelection(S#s.config_order),
    Assoc     = case wxRadioBox:getSelection(S#s.config_assoc) of
		    0 -> left;
		    1 -> right;
		    2 -> balanced;
		    3 -> none
		end,
    QType = recursive,
    %% _EdgeList = true,
    ?dbg("max  = ~p\n", [Max]),
    ?dbg("saturate = ~w\n", [Saturate]),
    ?dbg("backtrack = ~w\n", [Backtrack]),
    ?dbg("order = ~w\n", [Order]),
    ?dbg("assoc = ~w\n", [Assoc]),
    ?dbg("qtype = ~w\n", [QType]),
    ?dbg("timeout = ~w\n", [Timeout]),

    Formula = wxStyledTextCtrl:getText(S#s.formula),
    Meta = maps:from_list(Bound),
    case parse(Formula, Meta) of
	{ok,{Sections,Form}} ->
	    Options = [{method,count},{print,true},{timeout,Timeout},
		       {assoc,Assoc},{qtype,QType}],
	    GOpts = varp:load_option_list(Options),
	    GOpts1 = varp:section_opts(Sections, GOpts),
	    Do =
		[{wx,[{nbound,S#s.config_nbound},
		      {window,S#s.window},
		      {env, S#s.wx_env}]},
		 {Mode,[]}] ++
		case Saturate of
		    0 -> [];
		    _K -> [{saturate,[{level,1}]}]
		end ++
		case Order of
		    0 ->
			[{order,[{sort,[?ORDER_DEGREE bor ?ORDER_DESCEND]}]}];
		    1 ->
			[{order,[{sort,[?ORDER_RANK bor ?ORDER_DESCEND]}]}];
		    2 ->
			[{order,[{sort,[?ORDER_USER bor ?ORDER_DESCEND]}]}];
		    3 ->
			[{order,[{sort,[?ORDER_RANDOM]}]}];
		    4 ->
			%% pickup order from input file
			case maps:find(order, GOpts1) of
			    {ok, FileOrder} ->
				[{order, FileOrder}];
			    _ -> 
				[]
			end
		end ++
		case Backtrack of
		    0 ->
			[{backjump0, [{max,Max}]}];
		    1 ->
			[{backtrack,[{max,Max}]}];
		    2 ->
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

	    Res = (catch varp:do_run(GDo,Form,GOpts2)),

	    wxButton:enable(S#s.satisfy),
	    wxButton:enable(S#s.falsify),
	    wxButton:disable(S#s.cancel),

	    call(get(mon_proc), flush),
	    call(get(mon_proc), stop),

	    case Res of
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
		{'EXIT',{Err,_Where}} ->
		    output_error(S, varp:format_error(Err));
		Res ->
		    output_error(S, io_lib:format("unexpected ~p\n", [Res]))
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

%% add extension only if there no extension to the name
add_extension(Path, Ext) ->
    case filename:extension(Path) of
	"" -> Path ++ Ext;
	_ -> Path
    end.

export(Type, File, S) ->
    Meta  = wxTextCtrl:getValue(S#s.meta),
    case varp_scan:string(Meta) of
	{ok,Ts,_Ln} ->
	    case parse_bindings(Ts) of
		{ok,L} -> 
		    export(Type, File, S, L);
		{error,{_Ln,Reason,Mess1}} ->
		    Err = io_lib:format("~w ~p\n", 
					[Reason,Mess1]),
		    output_error(S, Err)
	    end;
	Error ->
	    Err = io_lib:format("~p", [Error]),
	    output_error(S, Err)
    end.

export(Type, File, S, Bound) ->
    Saturate  = wxSpinCtrl:getValue(S#s.config_saturate),
    Assoc     = case wxRadioBox:getSelection(S#s.config_assoc) of
		    0 -> left;
		    1 -> right;
		    2 -> balanced;
		    3 -> none
		end,
    Formula = wxStyledTextCtrl:getText(S#s.formula),
    Meta = maps:from_list(Bound),
    case parse(Formula, Meta) of
	{ok,{Sections,Form}} ->
	    Options = [{assoc,Assoc}],
	    GOpts = varp:load_option_list(Options),
	    GOpts1 = varp:section_opts(Sections, GOpts),
	    Do =
		[{satisfy,[]}] ++
		case Saturate of
		    0 -> [];
		    _K -> [{saturate,[{level,1}]}]
		end ++
		[{cnf, [{type,Type},{file,File},{symbols,true}]}],

	    GDo = varp:parse_do(Do),

	    GOpts2 = GOpts1#{ meta => Meta,
			      output => [{?MODULE,output_model,[S]}] },
	    output_clear(S),
	    ok = wxFrame:setStatusText(S#s.window, "export ok",[]),

	    Res = (catch varp:do_run(GDo,Form,GOpts2)),

	    case Res of
		{?CONTINUE, [], _Bs} ->
		    S;
		{?ERROR,_,_} ->
		    output_text(S, "ERROR\n");
		{'EXIT',{Err,_Where}} ->
		    output_error(S, varp:format_error(Err));
		Res ->
		    output_error(S, io_lib:format("unexpected ~p\n", [Res]))
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
output_model(_Fd, Model, S) ->
    wxStyledTextCtrl:setReadOnly(S#s.model, false),
    List = [ varp_formula:format_binding(B) || 
	       B <- varp_formula:filter_bindings(Model),
	       element(2,B) =/= false ],
    Chars = lists:join(",", List),
    wxStyledTextCtrl:addText(S#s.model, [Chars,"\n"]),
    wxStyledTextCtrl:setReadOnly(S#s.model, true),
    ok.

parse_bindings(Ts) ->
    parse_bindings_(Ts, []).

parse_bindings_([{identifier,_Ln1,Name},{'=',_Ln2},{decnum,_Ln3,Int}|Ts], Acc) ->
    parse_bindings_(Ts, [{Name, list_to_integer(Int,10)}|Acc]);
parse_bindings_([{identifier,_Ln1,Name},{'=',_Ln2},{hexnum,_Ln3,Int}|Ts], Acc) ->
    parse_bindings_(Ts, [{Name, list_to_integer(Int,16)}|Acc]);
parse_bindings_([{identifier,_Ln1,Name},{'=',_Ln2},{octnum,_Ln3,Int}|Ts], Acc) ->
    parse_bindings_(Ts, [{Name, list_to_integer(Int,8)}|Acc]);
parse_bindings_([{identifier,_Ln1,Name},{'=',_Ln2},{binnum,_Ln3,Int}|Ts], Acc) ->
    parse_bindings_(Ts, [{Name, list_to_integer(Int,2)}|Acc]);
parse_bindings_([{identifier,_Ln1,Name},{'=',_Ln2},{string,_Ln3,Str}|Ts], Acc) ->
    parse_bindings_(Ts, [{Name, Str}|Acc]);
parse_bindings_([{identifier,_Ln1,Name},{'=',_Ln2},{identifier,_Ln3,Str}|Ts], Acc) ->
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
    case varp:tokens(String) of
	{ok,[{identifier,_,"c"}|_Ts]} ->
	    parse_dimacs(String);
	{ok,[{identifier,_,"p"}|_Ts]} ->
	    parse_dimacs(String);
	{ok,Ts} ->
	    case varp_parse:parse(Ts) of
		{ok,{Sections,Formula}} ->
		    GOpts = #{ meta => Meta },
		    {ok, SectionMap} = varp:split_sections(Sections,GOpts),
		    {ok,{SectionMap,Formula}};
		Error -> Error
	    end;
	Error -> Error
    end.

parse_dimacs(String) ->
    Bin = list_to_binary(String), %% utf?
    case varp_dimacs:parse(Bin) of
	Form={cnf,{_Var,_Clause,SectionMap,_Units,_Cs}} ->
	    {ok,{SectionMap,Form}};
	Form={snf,{_Var,_Clause,SectionMap,_Units,_Cs}} ->
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
    Info = [atom,variable,number_of_variables,number_of_bound_variables,
	    number_of_clauses, number_of_dead_clauses],
    Ref = make_ref(),
    {Pid,Mon} =
	spawn_monitor(
	  fun() ->
		  ?dbg("varp_wx monitor ~p started\n", [self()]),
		  ok = varc:subscribe(Bs#bs.vp, Info),
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
	    update_info(Param,StartTime,Info1),
	    mon_loop(Bs,Param,Mon,StartTime,Info1);
	{varp, _X, Info} ->
	    ?dbg("varp_wx monitor: permanent (~w=1) ~s = ~w,info=~w\n", 
		 [_X,varp_formula:format_lit(Bs,_X), 1, Info]),
	    Info1 = mon_loop_collect(Info),
	    update_info(Param,StartTime,Info1),
	    mon_loop(Bs,Param,Mon,StartTime,Info1);
	Other ->
	    io:format("varp_wx monitor: got ~p\n", [Other]),
	    mon_loop(Bs,Param,Mon,StartTime,PrevInfo)
    after 1000 ->
	    Info1 = get_info(Bs),
	    Info2 = merge_info(Info1, PrevInfo),
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
	      number_of_clauses:=NC,
	      number_of_dead_clauses:=ND }) ->
    CurrentTime = erlang:monotonic_time(),
    Time = erlang:convert_time_unit(CurrentTime - StartTime,
				    native, millisecond),
    Status = io_lib:format(
	       "#Var: ~-8w #Bound: ~-8w #Clauses: ~-8w #Dead: ~-8w #Time: ~s",
	       [NV, NB, NC, ND, format_time(Time)]),
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

merge_info(#{ number_of_clauses := NC,
	      number_of_dead_clauses := ND}, Info2) ->
    %% max_level := L, max_bound := B
    Info2#{ number_of_clauses => NC,
	    number_of_dead_clauses => ND }.
%%	    max_level => L,
%%	    max_bound => B }.
    
get_info(Bs) ->
    #{ number_of_variables =>
	   varc:info(Bs#bs.vp,  number_of_variables),
       number_of_bound_variables => 
	   varc:info(Bs#bs.vp,number_of_bound_variables),
       number_of_clauses =>
	   varc:info(Bs#bs.vp,number_of_clauses),
       number_of_dead_clauses =>
	   varc:info(Bs#bs.vp,number_of_dead_clauses)
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
