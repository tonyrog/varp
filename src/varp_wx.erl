%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    wx GUI for varp
%%% @end
%%% Created : 15 Sep 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_wx).

-include_lib("wx/include/wx.hrl").

-export([start/0]).

start() ->
    Wx = wx:new(),
    Frame = wx:batch(fun() -> create_window(Wx) end),
    wxWindow:show(Frame),
    loop(Frame),
    wx:destroy(),
    ok.

-define(stc, wxStyledTextCtrl).

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

    %% create varp formula text area

    FixedFont = wxFont:new(10, ?wxFONTFAMILY_TELETYPE, ?wxNORMAL, ?wxNORMAL,[]),

    MainSizer = wxBoxSizer:new(?wxVERTICAL),
    Sizer = wxStaticBoxSizer:new(?wxVERTICAL, Frame, [{label, "meta"}]),
    
    TextCtrl  = wxTextCtrl:new(Frame, 1, [{value, "n=1,m=2; k=3 l=0"},
					  {style, ?wxDEFAULT}]),
    
    Ed = ?stc:new(Frame),
    ?stc:styleSetFont(Ed, ?wxSTC_STYLE_DEFAULT, FixedFont),
    ?stc:setLexer(Ed, ?wxSTC_LEX_NULL),
    ?stc:setMarginType(Ed, 0, ?wxSTC_MARGIN_NUMBER),
    LW = ?stc:textWidth(Ed, ?wxSTC_STYLE_LINENUMBER, "999"),
    ?stc:setMarginWidth(Ed, 0, LW),
    ?stc:setMarginWidth(Ed, 1, 0),
    ?stc:setSelectionMode(Ed, ?wxSTC_SEL_LINES),

    %% ?stc:styleSetFont(Ed, Style, FixedFont),
    %% ?stc:styleSetForeground(Ed, Style, {130,40,172}),

    ?stc:setKeyWords(Ed, 0, keyWords()),
    
    %% Scrolling
    Policy = ?wxSTC_CARET_SLOP bor ?wxSTC_CARET_JUMPS bor ?wxSTC_CARET_EVEN, 
    ?stc:setYCaretPolicy(Ed, Policy, 3),
    ?stc:setVisiblePolicy(Ed, Policy, 3), 
    %% ?stc:connect(Ed, stc_doubleclick),
    %% ?stc:connect(Ed, std_do_drop, fun(Ev, Obj) -> io:format("Ev ~p ~p~n",[Ev,Obj]) end),
    ?stc:setReadOnly(Ed, false),
    ?stc:setTextRaw(Ed, <<"[A x=1..10]P(x) or [A y=1..5]Q(y)", 0:8>>),

    ok = wxFrame:setStatusText(Frame, "Welcome to varp!",[]),

    wxSizer:add(Sizer, TextCtrl,  [{flag, ?wxEXPAND}]),
    wxSizer:add(MainSizer, Sizer, [{flag, ?wxEXPAND}]),
    wxSizer:addSpacer(MainSizer, 10),
    wxSizer:add(MainSizer, Ed, [{flag, ?wxEXPAND}, {proportion, 1}]),

    wxFrame:setSizer(Frame, MainSizer),

    Frame.


loop(Frame) ->
    receive 
        #wx{event=#wxClose{}} ->
            io:format("~p Closing window ~n",[self()]),
            wxFrame:destroy(Frame),
            ok;
        #wx{id=?wxID_EXIT, event=#wxCommand{type=command_menu_selected}} ->
            wxWindow:destroy(Frame),
            ok;
        #wx{id=?wxID_ABOUT, event=#wxCommand{type=command_menu_selected}} ->
            io:format("Got about ~n", []),
            dialog(?wxID_ABOUT, Frame),
            loop(Frame);
        Msg ->
            io:format("Got ~p ~n", [Msg]),
            loop(Frame)
    end.

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
