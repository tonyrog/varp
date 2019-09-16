%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    wx GUI for varp
%%% @end
%%% Created : 15 Sep 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_wx).

-include_lib("wx/include/wx.hrl").

-export([start/0]).

-record(s,
	{
	 frame,
	 meta,
	 formula,
	 model,
	 satisfy,
	 falsify
	}).

start() ->
    application:start(varp),
    Wx = wx:new(),
    S = wx:batch(fun() -> create_window(Wx) end),
    wxWindow:show(S#s.frame),
    loop(S),
    wx:destroy(),
    ok.


create_window(Wx) ->
    Frame = wxFrame:new(Wx, -1, "Varp", [{size, {600,400}}]),

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
    %%  | |Satisfy| |Falsify|         |
    %%  +-----------------------------+
    %%  |  Model (output)             |
    %%  |                             |
    %%  +-----------------------------+

    FixedFont = wxFont:new(10, ?wxFONTFAMILY_TELETYPE, ?wxNORMAL, ?wxNORMAL,[]),

    MainSizer = wxBoxSizer:new(?wxVERTICAL),
    MetaBox = wxStaticBoxSizer:new(?wxVERTICAL, Frame, [{label, "meta"}]),
    
    Meta = wxTextCtrl:new(Frame, 1, [{value, ""},
				     {style, ?wxDEFAULT}]),

    Formula = wxStyledTextCtrl:new(Frame),
    wxStyledTextCtrl:styleSetFont(Formula, ?wxSTC_STYLE_DEFAULT, FixedFont),
    wxStyledTextCtrl:setLexer(Formula, ?wxSTC_LEX_NULL), %% maybe CPP will color nice?
    wxStyledTextCtrl:setMarginType(Formula, 0, ?wxSTC_MARGIN_NUMBER),
    LW = wxStyledTextCtrl:textWidth(Formula, ?wxSTC_STYLE_LINENUMBER, "999"),
    wxStyledTextCtrl:setMarginWidth(Formula, 0, LW),
    wxStyledTextCtrl:setMarginWidth(Formula, 1, 0),
    wxStyledTextCtrl:setSelectionMode(Formula, ?wxSTC_SEL_LINES),
    wxStyledTextCtrl:setKeyWords(Formula, 0, keyWords()),
    Policy = ?wxSTC_CARET_SLOP bor ?wxSTC_CARET_JUMPS bor ?wxSTC_CARET_EVEN, 
    wxStyledTextCtrl:setYCaretPolicy(Formula, Policy, 3),
    wxStyledTextCtrl:setVisiblePolicy(Formula, Policy, 3),
    wxStyledTextCtrl:setReadOnly(Formula, false),
    %% TEST data
    %% wxStyledTextCtrl:setTextRaw(Formula, <<"[A x=1..n][E! y=1..m](P(x) and Q(y))", 0:8>>),

    %% BUTTONS

    Satisfy = wxButton:new(Frame, 10, [{label,"Satisfy"}]),
    wxButton:connect(Satisfy, command_button_clicked),
    Falsify = wxButton:new(Frame, 10, [{label,"Falsify"}]),
    wxButton:connect(Falsify, command_button_clicked),
    Buttons = wxBoxSizer:new(?wxHORIZONTAL),
    wxSizer:add(Buttons, Satisfy, []),
    wxSizer:add(Buttons, Falsify, []),

    %% MODEL output window

    Model = wxStyledTextCtrl:new(Frame),
    wxStyledTextCtrl:styleSetFont(Model, ?wxSTC_STYLE_DEFAULT, FixedFont),
    wxStyledTextCtrl:setLexer(Model, ?wxSTC_LEX_NULL),
    wxStyledTextCtrl:setMarginType(Model, 0, ?wxSTC_MARGIN_NUMBER),
    LW = wxStyledTextCtrl:textWidth(Model, ?wxSTC_STYLE_LINENUMBER, "999"),
    wxStyledTextCtrl:setMarginWidth(Model, 0, LW),
    wxStyledTextCtrl:setMarginWidth(Model, 1, 0),
    wxStyledTextCtrl:setSelectionMode(Model, ?wxSTC_SEL_LINES),
    Policy = ?wxSTC_CARET_SLOP bor ?wxSTC_CARET_JUMPS bor ?wxSTC_CARET_EVEN, 
    wxStyledTextCtrl:setYCaretPolicy(Model, Policy, 3),
    wxStyledTextCtrl:setVisiblePolicy(Model, Policy, 3),
    wxStyledTextCtrl:setReadOnly(Model, true),

    ok = wxFrame:setStatusText(Frame, "Welcome to varp!",[]),

    wxSizer:add(MetaBox, Meta,  [{flag, ?wxEXPAND}]),
    wxSizer:add(MainSizer, MetaBox, [{flag, ?wxEXPAND}]),
    wxSizer:addSpacer(MainSizer, 10),
    wxSizer:add(MainSizer, Formula, [{flag, ?wxEXPAND}, {proportion, 1}]),
    wxSizer:add(MainSizer, Buttons, []),
    wxSizer:add(MainSizer, Model,  [{flag, ?wxEXPAND}, {proportion, 1}]),

    wxFrame:setSizer(Frame, MainSizer),
    #s { frame = Frame, meta = Meta, formula = Formula, model = Model,
	 falsify = Falsify, satisfy = Satisfy }.


loop(S) ->
    io:format("Loop\n"),
    receive 
        #wx{event=#wxClose{}} ->
            io:format("~p Closing window ~n",[self()]),
            wxFrame:destroy(S#s.frame),
            ok;
        #wx{id=?wxID_EXIT, event=#wxCommand{type=command_menu_selected}} ->
            wxWindow:destroy(S#s.frame),
            ok;
        #wx{id=?wxID_OPEN, event=#wxCommand{type=command_menu_selected}} ->
	    Dialog = wxFileDialog:new(S#s.frame, []),
	    case wxFileDialog:showModal(Dialog) of
		?wxID_OK ->
		    Path = wxFileDialog:getPath(Dialog),
		    case file:read_file(Path) of
			{ok,Bin} ->
			    %% clear model
			    wxStyledTextCtrl:setReadOnly(S#s.model, false),
			    wxStyledTextCtrl:clearAll(S#s.model),
			    wxStyledTextCtrl:setReadOnly(S#s.model, true),
			    %% load formula text
			    %%  wxStyledTextCtrl:clearAll(S#s.formula),
			    wxStyledTextCtrl:setTextRaw(S#s.formula, <<Bin/binary,0>>),
			    loop(S);
			{error,Reason} ->
			    ok = wxFrame:setStatusText(S#s.frame, io_lib:format("file error: ~s ~p", [Path,Reason])),
			    loop(S)
		    end;
		?wxID_CANCEL ->
		    io:format("cancel\n"),
		    loop(S)
	    end;

        #wx{id=?wxID_ABOUT, event=#wxCommand{type=command_menu_selected}} ->
            io:format("Got about ~n", []),
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

run(Mode, S) ->
    Meta    = wxTextCtrl:getValue(S#s.meta),
    Bound   = case varp_scan:string(Meta) of
		  {ok,Ts,_Ln} ->
		      case parse_bindings(Ts) of
			  {ok,L} -> L;
			  _Err = {error,Ln,Message} ->
			      io:format("error:~w:~w\n", [Ln,Message]),
			      []
		      end;
		  _Error -> []
	      end,
    Formula = wxStyledTextCtrl:getText(S#s.formula),
    case parse(Formula) of
	{ok,{Sections,Form}} ->
	    Options = [{print,false}],
	    Do = [{Mode,[]}, {backtrack,[]}],
	    GDo = varp:parse_do(Do),
	    GOpts = varp:load_option_list(Options),
	    GOpts1 = varp:section_opts(Sections, GOpts#{ meta => Bound }),
	    try varp:do_run(GDo,Form,GOpts1) of
		{0,[]} ->
		    wxStyledTextCtrl:setReadOnly(S#s.model, false),
		    wxStyledTextCtrl:clearAll(S#s.model),
		    wxStyledTextCtrl:addText(S#s.model, "UNSATISFIABLE\n"),
		    wxStyledTextCtrl:setReadOnly(S#s.model, true),
		    S;
		{_N,Ms} ->
		    wxStyledTextCtrl:setReadOnly(S#s.model, false),
		    wxStyledTextCtrl:clearAll(S#s.model),
		    lists:foreach(
		      fun(M) ->
			      M1 = varp_formula:filter_bindings(M),
			      Chars = lists:join(",", [ varp_formula:format_binding(B) || 
							  B <- M1, element(2,B) =/= false ]),
			      wxStyledTextCtrl:addText(S#s.model, [Chars,"\n"])
		      end, Ms),
		    wxStyledTextCtrl:setReadOnly(S#s.model, true),
		    S;
		Res ->
		    io:format("Res=~w\n", [Res]),
		    S
	    catch
		error:Err ->
		    io:format("error ~p\n", [Err]),
		    S
	    end;
	Error ->
	    io:format("Parse error: ~p\n", [Error]),
	    S
    end.

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
		Error={error,{Ln,Mod,Why}} when 
		      is_integer(Ln), is_atom(Mod) ->
		    Reason = Mod:format_error(Why),
		    io:format("~w: ~s\n", [Ln,Reason]),
		    Error;
		Error ->
		    io:format("Error: ~p\n", [Error]),
		    Error
	    end;
	Error ->
	    io:format("Error: ~p\n", [Error]),
	    Error
    end.

tokens(String) ->
    case varp_scan:string(remove_comments(String)) of
	{ok,Ts,_Ln} -> 
	    {ok,Ts};
	Error -> 
	    io:format("token error ~p\n", [Error]),
	    Error
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
	 "and", "or", "xor", "not", "imp" "equ" "A" "E" "ALL" "ANY"
	 "SUM" "PROD"],
    lists:flatten([K ++ " " || K <- L] ++ [0]).
