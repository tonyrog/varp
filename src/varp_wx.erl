%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    wx GUI for varp
%%% @end
%%% Created : 15 Sep 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_wx).

-include_lib("wx/include/wx.hrl").

-export([start/0]).
-export([output_model/3]).  %% varp callback

%% warp_wx is also a plugin (monitor assignment etc)
-export([options/0, run/2]).

-include("varp.hrl").

-record(s,
	{
	 window,
	 meta,
	 formula,
	 model,
	 satisfy,
	 falsify,
	 cancel,
	 dir = "",
	 wx_env,            %% environment passed to plugin 
	 %% config
	 config_max_models, %% wxSpinCtrl
	 config_timeout,    %% wxSpinCtrl
	 config_saturate,   %% wxSpinCtrl (saturate=1 or none=0)
	 config_backtrack,  %% wxRadioBox (backtrack|backjump|none)
	 config_order,      %% wxRadioBox (-degree|-rank|none)
	 config_assoc,      %% wxRadioBox (left|right|balanced|none)
	 config_nbound      %% wxGauge
	}).

version() ->
    {ok,Vsn} = application:get_key(varp, vsn),
    Vsn.

start() ->
    application:start(varp),
    application:load(wx),
    spawn(
      fun() ->
	      Wx = wx:new(),
	      %% try wx:batch(fun() -> create_window(Wx) end) of
	      try create_window(Wx) of
		  S ->
		      wxWindow:show(S#s.window),
		      loop(S),
		      wx:destroy(),
		      erlang:halt()
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
    wxFrame:connect(Window, close_window),

    MenuBar  = wxMenuBar:new(),
    FileM    = wxMenu:new([]),
    HelpM    = wxMenu:new([]),

    % unlike wxwidgets the stock menu items still need text to be given, 
    % although help text does appear
    _OpenMenuItem  = wxMenu:append(FileM, ?wxID_OPEN, "&Open"),
    _SaveMenuItem  = wxMenu:append(FileM, ?wxID_SAVE, "&Save"),
    _SaveAsMenuItem  = wxMenu:append(FileM, ?wxID_SAVEAS, "&Save As..."),
    _QuitMenuItem  = wxMenu:append(FileM, ?wxID_EXIT, "&Quit"),
    % Note the keybord accelerator
    _AboutMenuItem = wxMenu:append(HelpM, ?wxID_ABOUT, "&About...\tF1"),

    wxMenu:appendSeparator(HelpM),
    ContentsMenuItem = wxMenu:append(HelpM, ?wxID_HELP_CONTENTS, "&Contents"),
    wxMenuItem:enable(ContentsMenuItem, [{enable, false}]),

    ok = wxFrame:connect(Window, command_menu_selected),

    wxMenuBar:append(MenuBar, FileM, "&File"),
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
    SmallFont = wxFont:new(8, ?wxFONTFAMILY_TELETYPE, ?wxNORMAL, ?wxNORMAL,[]),

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
    %% wxStyledTextCtrl:setCaretLineBackAlpha(Formula, 127),

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

    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    %% WINDOW 2
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    Sizer2 = wxBoxSizer:new(?wxVERTICAL),

    %% BUTTONS
    Run = wxStaticBoxSizer:new(?wxHORIZONTAL,Win2,[{label, "run"}]),
    Satisfy = wxButton:new(Win2, 10, [{label,"Satisfy"}]),
    wxButton:connect(Satisfy, command_button_clicked),

    Falsify = wxButton:new(Win2, 11, [{label,"Falsify"}]),
    wxButton:connect(Falsify, command_button_clicked),

    Cancel = wxButton:new(Win2, 12, [{label,"Cancel"}]),
    SELF = self(),
    wxButton:connect(Cancel, command_button_clicked,
		     [{callback,
		       fun(_Event,_Object) -> 
			       SELF ! {cancel, self()}
		       end }]),
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
			   ["-degree", "-rank", "none"],
			   [{majorDim, 1},{style,  ?wxVERTICAL}]),

    Assoc = wxRadioBox:new(Win2, 23, "assoc",
			   ?wxDefaultPosition,
			   ?wxDefaultSize,
			   ["left", "right", "balanced", "none"],
			   [{majorDim, 1},{style,  ?wxVERTICAL}]),

    NBound = wxGauge:new(Win2, 31, 100, [{size,{800,10}},
					 {style, ?wxGA_HORIZONTAL}]),

    %% wxRadioBox:connect(ModelMode, command_radiobox_selected),
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

    {ok, DefaultDir} = file:get_cwd(),  %% fixme: save dir?
    #s { window = Window, 
	 meta = Meta, 
	 formula = Formula, 
	 model = Model,
	 falsify = Falsify, 
	 satisfy = Satisfy,
	 cancel = Cancel,
	 dir = DefaultDir,
	 config_max_models = MaxModels,
	 config_timeout    = Timeout,
	 config_saturate   = Saturate,
	 config_backtrack  = Backtrack,
	 config_order      = Order,
	 config_assoc      = Assoc,
	 config_nbound     = NBound,
	 wx_env            = wx:get_env()
       }.

loop(S) ->
    receive 
        #wx{event=#wxClose{}} ->
            wxFrame:destroy(S#s.window),
            ok;
        #wx{id=?wxID_EXIT, event=#wxCommand{type=command_menu_selected}} ->
            wxWindow:destroy(S#s.window),
            ok;
        #wx{id=?wxID_OPEN, event=#wxCommand{type=command_menu_selected}} ->
	    Dialog = wxFileDialog:new(S#s.window,
				      [{defaultDir,S#s.dir},
				       {wildCard, 
					"*.varp;*.cnf;*.snf;*.txt"}]),
	    case wxFileDialog:showModal(Dialog) of
		?wxID_OK ->
		    Path = wxFileDialog:getPath(Dialog),
		    case file:read_file(Path) of
			{ok,Bin} ->
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
			    loop(S#s { dir = Dir });
			{error,Reason} ->
			    Text = io_lib:format("file error: ~s ~p",
						 [Path,Reason]),
			    ok = wxFrame:setStatusText(S#s.window, Text),
			    loop(S)
		    end;
		?wxID_CANCEL ->
		    loop(S)
	    end;

        #wx{id=?wxID_ABOUT, event=#wxCommand{type=command_menu_selected}} ->
            dialog(?wxID_ABOUT, S#s.window),
            loop(S);

        #wx{event=#wxSplitter{type=command_splitter_sash_pos_changed}} ->
	    io:format("Splitter pos changed\n"),
            loop(S);

        Msg = #wx{obj=Obj, event=#wxCommand{type=command_button_clicked}} ->	
	    if S#s.satisfy =:= Obj ->
		    S1 = satisfy(S),
		    loop(S1);
	       S#s.falsify =:= Obj ->
		    S1 = falsify(S),
		    loop(S1);
	       true ->
		    io:format("Got command_button_clicked ~p ~n", [Msg]),
		    loop(S)
	    end;
        Msg ->
            io:format("Got ~p ~n", [Msg]),
            loop(S)
    end.

satisfy(S) ->
    solve(satisfy, S).

falsify(S) ->
    solve(falsify, S).

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
    Mon = 
	spawn(
	  fun() ->
		  io:format("varp_wx monitor ~p started\n", [self()]),
		  varc:subscribe(Bs#bs.vp, atom),
		  Mon = monitor(process, SELF),
		  wx:set_env(maps:get(env, Param)),
		  update_nbound(Bs, Param),
		  mon_loop(Bs, Param, Mon)
	  end),
    put(mon_proc, Mon),
    {?CONTINUE,[],Bs}.
    
mon_loop(Bs,Param,Mon) ->
    receive
	{'DOWN', Mon, process, _Pid, _Reason} ->
	    done;
	{varp, {X,Y}} ->
	    io:format("varp_wx monitor: substitut (~w=>~w) ~s => ~s\n", 
		      [Y,X,
		       varp_formula:format_lit(Bs,Y),
		       varp_formula:format_lit(Bs,X)]),
	    update_nbound(Bs, Param),
	    mon_loop(Bs,Param,Mon);
	{varp, X} ->
	    io:format("varp_wx monitor: permanent (~w=1) ~s = ~w\n", 
		      [X,varp_formula:format_lit(Bs,X), 1]),
	    update_nbound(Bs, Param),
	    mon_loop(Bs,Param,Mon);
	Other ->
	    io:format("varp_wx monitor: got ~p\n", [Other]),
	    mon_loop(Bs,Param,Mon)
    end.

update_nbound(Bs,#{nbound:=NBound, window:=Window}) ->
    NV = varp_formula:number_of_variables(Bs),
    NB = varp_formula:number_of_bound(Bs),
    Percent = 100*(NB/NV),
    NC = varp_formula:number_of_clauses(Bs),
    Status = io_lib:format("#Var: ~w, #Bound: ~w, #Clauses: ~w", [NV, NB, NC]),
    wxGauge:setValue(NBound, trunc(Percent)),
    wxFrame:setStatusText(Window, Status,[]).


%% FIXME block interface while running
solve(Mode, S) ->
    Meta  = wxTextCtrl:getValue(S#s.meta),
    case varp_scan:string(Meta) of
	{ok,Ts,_Ln} ->
	    case parse_bindings(Ts) of
		{ok,L} -> solve(Mode, S, L);
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
    ?dbg("meta = ~p\n", [Meta]),
    ?dbg("max  = ~p\n", [Max]),
    ?dbg("saturate = ~w\n", [Saturate]),
    ?dbg("backtrack = ~w\n", [Backtrack]),
    ?dbg("order = ~w\n", [Order]),
    ?dbg("assoc = ~w\n", [Assoc]),
    ?dbg("qtype = ~w\n", [QType]),
    ?dbg("timeout = ~w\n", [Timeout]),

    Formula = wxStyledTextCtrl:getText(S#s.formula),
    case parse(Formula) of
	{ok,{Sections,Form}} ->
	    %% io:format("Form = ~p\n", [Form]),
	    %% io:format("Sections = ~p\n", [Sections]),
	    %% method=count,print=true,output={M,F,A} will allow 
	    %% to display models in the window without output without
	    %% storing them in memory.
	    Options = [{method,count},{print,true},{timeout,Timeout},
		       {assoc,Assoc},{qtype,QType}],
	    GOpts = varp:load_option_list(Options),
	    GOpts1 = varp:section_opts(Sections, GOpts),
	    Do =
		[{Mode,[]},
		 {wx,[{nbound,S#s.config_nbound},
		      {window,S#s.window},
		      {env, S#s.wx_env}]}
		] ++
		case Saturate of
		    0 -> [];
		    _K -> [{saturate,[{level,1}]}]
		end ++
		case Order of
		    0 ->
			[{order,[{sort,['-degree']}]}];
		    1 ->
			[{order,[{sort,['-rank']}]}];
		    2 ->
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
			[{backjump, [{max,Max}]}];
		    1 ->
			[{backtrack,[{max,Max}]}];
		    2 ->
			[]
		end,

	    GDo = varp:parse_do(Do),

	    GOpts2 = GOpts1#{ meta => Bound,
			      output => [{?MODULE,output_model,[S]}] },
	    output_clear(S),
	    ok = wxFrame:setStatusText(S#s.window, "ok",[]),
	    %% wxStyledTextCtrl:setCaretLineVisible(S#s.formula, false),

	    wxButton:disable(S#s.satisfy),
	    wxButton:disable(S#s.falsify),
	    wxButton:enable(S#s.cancel),

	    Res = (catch varp:do_run(GDo,Form,GOpts2)),

	    wxButton:enable(S#s.satisfy),
	    wxButton:enable(S#s.falsify),
	    wxButton:disable(S#s.cancel),

	    exit(get(mon_proc), kill),

	    case Res of
		{?INCONSISTENT,_,_Bs} ->
		    output_text(S, "UNSATISFIABLE\n");
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
		{'EXIT',{{unbound,Var}, _Where}} ->
		    output_error(S, ["Variable ", Var, " is unbound\n"]);
		{'EXIT',Err} ->
		    output_error(S, io_lib:format("~p\n", [Err]));
		Res ->
		    output_error(S, io_lib:format("unexpected ~p\n", [Res]))
	    end;
	{error, Line, Message} ->
	    Pos = wxStyledTextCtrl:positionFromLine(S#s.formula, Line-1),
	    io:format("Error Line: line=~w, pos=~w\n", [Line, Pos]),
	    %% wxStyledTextCtrl:setCurrentPos(S#s.formula, Pos),
	    %% wxStyledTextCtrl:setCaretLineVisible(S#s.formula, true),
	    output_error(S, Message);
	{error, Message} ->
	    output_error(S, Message)
    end.

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

parse(String) ->
    case varp:tokens(String) of
	{ok,[{identifier,_,"c"}|_Ts]} ->
	    parse_dimacs(String);
	{ok,[{identifier,_,"p"}|_Ts]} ->
	    parse_dimacs(String);
	{ok,Ts} ->
	    case varp_parse:parse(Ts) of
		{ok,{Sections,Formula}} ->
		    SectionMap = varp:split_sections(Sections),
		    {ok,{SectionMap,Formula}};
		{error,{Ln,Mod,Why}} when 
		      is_integer(Ln), is_atom(Mod) ->
		    Reason = Mod:format_error(Why),
		    {error, Ln, Reason};
		{error,Reason} ->
		    {error, io_lib:format("~p\n", [Reason])}
	    end;
	{error,Reason}->
	    {error, io_lib:format("~p\n", [Reason])}
    end.

parse_dimacs(String) ->
    Bin = list_to_binary(String), %% utf?
    case varp_dimacs:parse(Bin) of
	Form={cnf,{_Var,_Clause,SectionMap,_Units,_Cs}} ->
	    {ok,{SectionMap,Form}};
	Form={snf,{_Var,_Clause,SectionMap,_Units,_Cs}} ->
	    {ok,{SectionMap,Form}};
	Error -> Error
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
	 "symbol", "true", "false", "define", "declare", "literals",
	 "assert", "input", "output", "order", "rank", "degree", 
	 "random", "identity",
	 "and", "or", "xor", "not", "imp", "equ", "A", "E", "ALL", "ANY",
	 "SUM", "PROD"],
    lists:flatten([K ++ " " || K <- L] ++ [0]).
