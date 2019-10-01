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

-include("varp.hrl").

-record(s,
	{
	 frame,
	 meta,
	 formula,
	 model,
	 satisfy,
	 falsify,
	 cancel,
	 dir = "",
	 %% config
	 config_max_models, %% wxSpinCtrl
	 config_timeout,    %% wxSpinCtrl
	 config_saturate,   %% wxSpinCtrl (saturate=1 or none=0)
	 config_backtrack,  %% wxRadioBox (backtrack|backjump|none)
	 config_order       %% wxRadioBox (-degree|-rank|none)
	}).

start() ->
    application:start(varp),
    application:load(wx),
    spawn(
      fun() ->
	      Wx = wx:new(),
	      S = wx:batch(fun() -> create_window(Wx) end),
	      wxWindow:show(S#s.frame),
	      loop(S),
	      wx:destroy(),
	      erlang:halt()
      end).


create_window(Wx) ->
    Frame = wxFrame:new(Wx, -1, "Varp", [{size, {800,600}}]),

    Path = code:priv_dir(varp),
    wxFrame:setIcon(Frame,  wxIcon:new(filename:join(Path,"varp.png"),
				       [{type, ?wxBITMAP_TYPE_PNG}])),

    wxFrame:createStatusBar(Frame,[]),
    wxFrame:connect(Frame, close_window),

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

    ok = wxFrame:connect(Frame, command_menu_selected),

    wxMenuBar:append(MenuBar, FileM, "&File"),
    wxMenuBar:append(MenuBar, HelpM, "&Help"),
    wxFrame:setMenuBar(Frame, MenuBar),

    %% Create varp GUI
    %%  +-----------------------------+
    %%  |  Meta (input)               |
    %%  +-----------------------------+
    %%  |  Formula (input)            |
    %%  |                             |
    %%  |                             |
    %%  |                             |
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

    MainSizer = wxBoxSizer:new(?wxVERTICAL),
    MetaBox = wxStaticBoxSizer:new(?wxVERTICAL, Frame, [{label, "meta"}]),
    
    Meta = wxTextCtrl:new(Frame, 1, [{value, ""},
				     {style, ?wxDEFAULT}]),

    Formula = wxStyledTextCtrl:new(Frame),
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

    %% BUTTONS
    Run = wxStaticBoxSizer:new(?wxHORIZONTAL, Frame, [{label, "run"}]),
    Satisfy = wxButton:new(Frame, 10, [{label,"Satisfy"}]),
    wxButton:connect(Satisfy, command_button_clicked),

    Falsify = wxButton:new(Frame, 11, [{label,"Falsify"}]),
    wxButton:connect(Falsify, command_button_clicked),

    Cancel = wxButton:new(Frame, 12, [{label,"Cancel"}]),
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
    MaxBox = wxStaticBoxSizer:new(?wxVERTICAL,Frame,[{label, "max"}]),
    MaxModels = wxSpinCtrl:new(Frame, []),
    wxSpinCtrl:setRange(MaxModels, 1, 1000),
    wxSizer:add(MaxBox, MaxModels),

    TimeBox = wxStaticBoxSizer:new(?wxVERTICAL,Frame,[{label,"timeout"}]),
    Timeout = wxSpinCtrl:new(Frame, []),
    wxSpinCtrl:setRange(Timeout, 0, 100000),
    wxSizer:add(TimeBox, Timeout),

    SaturateBox = wxStaticBoxSizer:new(?wxVERTICAL,Frame,[{label,"saturate"}]),
    Saturate = wxSpinCtrl:new(Frame, []),
    wxSpinCtrl:setRange(Saturate, 0, 3),
    wxSizer:add(SaturateBox, Saturate),

    %% SmallFont = wxFont:new(8, ?wxFONTFAMILY_TELETYPE, ?wxNORMAL, ?wxNORMAL,[]),
    Backtrack = wxRadioBox:new(Frame, 1, "backtrack",
			       ?wxDefaultPosition,
			       ?wxDefaultSize,
			       ["backjump","backtrack","none"],
			       [{majorDim, 1}, {style, ?wxVERTICAL}]),

    Order = wxRadioBox:new(Frame, 1, "order",
			   ?wxDefaultPosition,
			   ?wxDefaultSize,
			   ["-degree", "-rank", "none"],
			   [{majorDim, 1},{style,  ?wxVERTICAL}]),



    %% wxRadioBox:connect(ModelMode, command_radiobox_selected),
    Config = wxBoxSizer:new(?wxVERTICAL),
    Config1 = wxBoxSizer:new(?wxHORIZONTAL),
    Config2 = wxBoxSizer:new(?wxHORIZONTAL),

    wxSizer:add(Config, Config1, []),
    wxSizer:add(Config, Config2, []),
    wxSizer:add(Config1, Run, []),
    wxSizer:add(Config1, MaxBox, []),
    wxSizer:add(Config1, TimeBox, []),
    wxSizer:add(Config1, SaturateBox, []),
    
    wxSizer:add(Config2, Backtrack, []),
    wxSizer:add(Config2, Order, []),

    %% MODEL output window

    Model = wxStyledTextCtrl:new(Frame),
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

    ok = wxFrame:setStatusText(Frame, "ok",[]),

    wxSizer:add(MetaBox, Meta,  [{flag, ?wxEXPAND}]),
    wxSizer:add(MainSizer, MetaBox, [{flag, ?wxEXPAND}]),
    wxSizer:addSpacer(MainSizer, 10),
    wxSizer:add(MainSizer, Formula, [{flag, ?wxEXPAND}, {proportion, 1}]),
    wxSizer:add(MainSizer, Config, []),
    wxSizer:add(MainSizer, Model,  [{flag, ?wxEXPAND}, {proportion, 1}]),

    wxFrame:setSizer(Frame, MainSizer),
    {ok, DefaultDir} = file:get_cwd(),  %% fixme: save dir?
    #s { frame = Frame, 
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
	 config_order      = Order
       }.


loop(S) ->
    receive 
        #wx{event=#wxClose{}} ->
            wxFrame:destroy(S#s.frame),
            ok;
        #wx{id=?wxID_EXIT, event=#wxCommand{type=command_menu_selected}} ->
            wxWindow:destroy(S#s.frame),
            ok;
        #wx{id=?wxID_OPEN, event=#wxCommand{type=command_menu_selected}} ->
	    Dialog = wxFileDialog:new(S#s.frame,
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
			    ok = wxFrame:setStatusText(S#s.frame, Text),
			    loop(S)
		    end;
		?wxID_CANCEL ->
		    loop(S)
	    end;

        #wx{id=?wxID_ABOUT, event=#wxCommand{type=command_menu_selected}} ->
            dialog(?wxID_ABOUT, S#s.frame),
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
    run(satisfy, S).

falsify(S) ->
    run(falsify, S).

%% FIXME block interface while running
run(Mode, S) ->
    Meta      = wxTextCtrl:getValue(S#s.meta),
    Max       = wxSpinCtrl:getValue(S#s.config_max_models),
    Timeout   = case wxSpinCtrl:getValue(S#s.config_timeout) of
		    0 -> infinity;
		    T -> T
		end,
    Saturate  = wxSpinCtrl:getValue(S#s.config_saturate),
    Backtrack = wxRadioBox:getSelection(S#s.config_backtrack),
    Order     = wxRadioBox:getSelection(S#s.config_order),
    ?dbg("meta = ~p\n", [Meta]),
    ?dbg("max  = ~p\n", [Max]),
    ?dbg("saturate = ~w\n", [Saturate]),
    ?dbg("backtrack = ~w\n", [Backtrack]),
    ?dbg("order = ~w\n", [Order]),
    ?dbg("timeout = ~w\n", [Timeout]),
    Bound = case varp_scan:string(Meta) of
		{ok,Ts,_Ln} ->
		      case parse_bindings(Ts) of
			  {ok,L} -> L;
			  _Err = {error,Ln1,Mess1} ->
			      io:format("error:~w:~w\n", [Ln1,Mess1]),
			      []
		      end;
		  _Error -> []
	      end,
    Formula = wxStyledTextCtrl:getText(S#s.formula),
    case parse(Formula) of
	{ok,{Sections,Form}} ->
	    %% method=count,print=true,output={M,F,A} will allow 
	    %% to display models in the window without output without
	    %% storing them in memory.
	    Options = [{method,count},{print,true},{timeout,Timeout}],
	    GOpts = varp:load_option_list(Options),
	    GOpts1 = varp:section_opts(Sections, GOpts),
	    Do =
		[{Mode,[]}] ++
		case Saturate of
		    0 -> [];
		    _K -> [{saturate,[{level,1}]}]  %% fixme set level
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
				%% io:format("Order = ~w\n", [FileOrder]),
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
	    ok = wxFrame:setStatusText(S#s.frame, "ok",[]),
	    %% wxStyledTextCtrl:setCaretLineVisible(S#s.formula, false),

	    wxButton:disable(S#s.satisfy),
	    wxButton:disable(S#s.falsify),
	    wxButton:enable(S#s.cancel),

	    Res = (catch varp:do_run(GDo,Form,GOpts2)),

	    wxButton:enable(S#s.satisfy),
	    wxButton:enable(S#s.falsify),
	    wxButton:disable(S#s.cancel),

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
    ok = wxFrame:setStatusText(S#s.frame, "Error",[]),
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
    case tokens(String) of
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

tokens(String) ->
    case varp_scan:string(remove_comments(String)) of
	{ok,Ts,_Ln} -> 
	    {ok,Ts};
	{error,{_Ln1,Mod,Why},_Ln2} -> 
	    Reason = Mod:format_error(Why),
	    {error, Reason};
	{error,Reason} -> 
	    {error, io_lib:format("~p\n", [Reason])}
    end.

%% remove C-style comments from data
remove_comments([$/,$/|Cs]) -> remove_comments(remove_line(Cs));
remove_comments([$/,$*|Cs]) -> remove_comments(remove_block(Cs));
remove_comments([C|Cs]) -> [C|remove_comments(Cs)];
remove_comments([]) -> [].

%% remove until */ but keep all \n
remove_block([$*,$/|Cs]) -> Cs;
remove_block([$\n|Cs]) -> [$\n|remove_block(Cs)];
remove_block([_|Cs]) -> remove_block(Cs);
remove_block([]) -> [].

%% remove until end-of-line (but keep it)
remove_line(Cs=[$\n|_]) -> Cs;
remove_line([_|Cs]) -> remove_line(Cs);
remove_line([]) -> [].



dialog(?wxID_ABOUT,  Frame) ->
    Str = string:join(["Varp.", 
                       "Varp is a propositional theorem prover\n",
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
