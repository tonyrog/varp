%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    Show settings dialog
%%% @end
%%% Created : 17 Dec 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_wx_settings).

-include_lib("wx/include/wx.hrl").

-export([setup/1]).

-export([test/0]).
-export([main_loop/1]).


-include("varp.hrl").


-record(backjump,
	{
	 minimize,               %% wxCheckBox
	 iorder,                 %% wxSpinCtrl
	 stumble,                %% wxSpinCtrl
	 olle,                   %% wxStaticBoxSizer
	 stumble_olle,           %% wxCheckBox
	 max_conflicts,          %% wxSpinCtrl
	 max_learned,            %% wxSpinCtrl
	 max_learned_factor,     %% wxStaticBoxSizer
	 max_learned_inc,        %% wxStaticBoxSizer
	 keep_factor,            %% wxStaticBoxSizer
	 min_keep_clauses,       %% wxSpinCtrl
	 restart_counter,        %% wxSpinCtrl
	 restart_interval        %% wxSpinCtrl
	}).

-record(settings,
	{
	 backtrack,
	 assoc,
	 order,
	 order_1,
	 order_2,
	 backjump
	}).


setup(Parent) ->
    Panel = wxPanel:new(Parent, []),

    %% Setup sizers
    MainSizer = wxStaticBoxSizer:new(?wxVERTICAL, Panel, 
				     [{label, "Settings"}]),

    Notebook = wxNotebook:new(Panel, 1, [{style, ?wxBK_DEFAULT%,
					        %?wxBK_ALIGN_MASK,
					        %?wxBK_TOP,
					        %?wxBK_BOTTOM,
					        %?wxBK_LEFT,
					        %?wxBK_RIGHT,
					        %?wxNB_MULTILINE % windows only
					 }]),

    %% Add to sizers
    wxSizer:add(MainSizer, Notebook, [{proportion, 1},
				      {flag, ?wxEXPAND}]),
    wxNotebook:connect(Notebook, command_notebook_page_changed,
		       [{skip, true}]), % {skip, true} has to be set on windows
    wxPanel:setSizer(Panel, MainSizer),

    Settings = 
	[setup_settings(Notebook,integer_to_list(I)) || I <- lists:seq(1,10)],
    {Panel,Settings}.

setup_settings(Notebook, Name) ->
    Panel = wxPanel:new(Notebook, []),
    {Config,Si} = varp_settings(Panel),
    wxPanel:setSizer(Panel, Config),
    wxNotebook:addPage(Notebook, Panel, Name, []),
    Si.

varp_settings(Parent) ->
    Backtrack = varp_settings_backtrack(Parent),
    Assoc = varp_settings_assoc(Parent),
    {Order,Order1,Order2} = varp_settings_order(Parent),
    {Backjump, Bj} = varp_settings_backjump(Parent),
    Config = wxBoxSizer:new(?wxVERTICAL),
    Config1 = wxBoxSizer:new(?wxHORIZONTAL),
    Config2 = wxBoxSizer:new(?wxHORIZONTAL),
    Config3 = wxBoxSizer:new(?wxHORIZONTAL),
    wxSizer:add(Config, Config1, [{border,4},{flag,?wxALL}]),
    wxSizer:add(Config, Config2, [{border,4},{flag,?wxALL}]),
    wxSizer:add(Config, Config3, [{border,4},{flag,?wxALL}]),
    wxSizer:add(Config1, Backtrack, [{border,4},{flag,?wxALL}]),
    wxSizer:add(Config1, Assoc, [{border,4},{flag,?wxALL}]),
    wxSizer:add(Config2, Order, [{border,4},{flag,?wxALL}]),
    wxSizer:add(Config3, Backjump, [{border,4},{flag,?wxALL}]),

    {Config,
     #settings {
	backtrack = Backtrack,
	assoc = Assoc,
	order = Order,
	order_1 = Order1,
	order_2 = Order2,
	backjump = Bj
       }}.

%% select backjump(default) backtrack or none
varp_settings_backtrack(Parent) ->
    Backtrack = wxRadioBox:new(Parent, ?wxID_ANY, "Backtrack",
			       ?wxDefaultPosition,
			       ?wxDefaultSize,
			       ["Backjump","Backtrack","None"],
			       [{majorDim, 1}, {style, ?wxVERTICAL}]),
    Backtrack.

varp_settings_assoc(Parent) ->
    Assoc = wxRadioBox:new(Parent, ?wxID_ANY, "Assoc",
			   ?wxDefaultPosition,
			   ?wxDefaultSize,
			   ["Left", "Right", "Mid", "None"],
			   [{majorDim,1},{style,?wxVERTICAL}]),
    Assoc.


%% Select global sort order (mainly for fix order backtracking)
varp_settings_order(Parent) ->
    Order = wxStaticBoxSizer:new(?wxVERTICAL,Parent,[{label,"Order"}]),
    Order1 = wxBoxSizer:new(?wxHORIZONTAL),
    B10 = wxCheckBox:new(Parent,?wxID_ANY,"",
			 [{style, ?wxCHK_3STATE bor
			       ?wxCHK_ALLOW_3RD_STATE_FOR_USER}]),
    wxCheckBox:set3StateValue(B10, ?wxCHK_UNDETERMINED),
    B11 = wxRadioButton:new(Parent,?wxID_ANY,"Deg",[{style,?wxRB_GROUP}]),
    B12 = wxRadioButton:new(Parent,?wxID_ANY,"Rank",[]),
    B13 = wxRadioButton:new(Parent,?wxID_ANY,"User",[]),
    B14 = wxRadioButton:new(Parent,?wxID_ANY,"Rand",[]),
    B15 = wxRadioButton:new(Parent,?wxID_ANY,"Id",[]),
    Order1List = [B10,B11,B12,B13,B14,B15],
    [wxSizer:add(Order1, Bi) || Bi <- Order1List],

    Order2 = wxBoxSizer:new(?wxHORIZONTAL),
    B20 = wxCheckBox:new(Parent,?wxID_ANY,"",
			 [{style, ?wxCHK_3STATE bor
			       ?wxCHK_ALLOW_3RD_STATE_FOR_USER}]),
    wxCheckBox:set3StateValue(B20, ?wxCHK_UNDETERMINED),
    B21 = wxRadioButton:new(Parent,?wxID_ANY,"Deg",[{style,?wxRB_GROUP}]),
    B22 = wxRadioButton:new(Parent,?wxID_ANY,"Rank",[]),
    B23 = wxRadioButton:new(Parent,?wxID_ANY,"User",[]),
    B24 = wxRadioButton:new(Parent,?wxID_ANY,"Rand",[]),
    B25 = wxRadioButton:new(Parent,?wxID_ANY,"Id",[]),
    Order2List = [B20,B21,B22,B23,B24,B25],
    [wxSizer:add(Order2, Bi) || Bi <- Order2List],
    wxSizer:add(Order, Order1),
    wxSizer:add(Order, Order2),
    {Order, Order1List, Order2List}.

varp_settings_backjump(Parent) ->
    Backjump = wxStaticBoxSizer:new(?wxHORIZONTAL,Parent,
				    [{label,"Backjump"}]),
    Column1 = wxBoxSizer:new(?wxVERTICAL),
    Column2 = wxBoxSizer:new(?wxVERTICAL),
    Column3 = wxBoxSizer:new(?wxVERTICAL),

    Minimize = wxCheckBox:new(Parent,?wxID_ANY,"Minimize",[]),
    {IOrder,IOrderSizer} = varpSpinCtrl(Parent, 0, 100,
					"Max clause length", ""),
    {Stumble,StumbleSizer} = varpSpinCtrl(Parent, 0, 100,
					  "Stumble", ""),
    {Olle,OlleSizer} = varpNumber(Parent, 0.0, 100.0, "Olle", ""),
    StumbleAndOlle = wxCheckBox:new(Parent,?wxID_ANY,"Stumble&Olle",[]),
    {MaxConflicts,MaxConflictsSizer} = varpSpinCtrl(Parent, 0, 10, 
						    "max conflicts", ""),
    {MaxLearned,MaxLearnedSizer} = varpSpinCtrl(Parent, 0, 1000000,
						"Max learned clauses", ""),
    {MaxLearnedFactor,MaxLearnedFactorSizer} =
	varpNumber(Parent, 0.0, 100.0, "Max learned factor", ""),
    {MaxLearnedInc,MaxLearnedIncSizer} =
	varpNumber(Parent, 1.0, 100.0, "Max learned inc", ""),

    {RestartCounter,RestartCounterSizer} =
	varpSpinCtrl(Parent, 0, 10, "Restart counter", ""),
    {RestartInterval,RestartIntervalSizer} =
	varpSpinCtrl(Parent, 0, 100000, "Restart Interval", ""),

    wxSizer:add(Backjump, Column1, [{border,4},{flag,?wxRIGHT}]),
    wxSizer:add(Backjump, Column2, [{border,4}]),
    wxSizer:add(Backjump, Column3, [{border,4},{flag,?wxLEFT}]),

    wxSizer:add(Column1, Minimize, [{border,4},{flag,?wxDOWN}]),
    wxSizer:add(Column1, IOrderSizer, [{border,4},{flag,?wxDOWN}]),
    wxSizer:add(Column1, MaxConflictsSizer, [{border,4}]),

    wxSizer:add(Column2, StumbleAndOlle, [{border,4},{flag,?wxDOWN}]),
    wxSizer:add(Column2, StumbleSizer, [{border,4},{flag,?wxDOWN}]),
    wxSizer:add(Column2, OlleSizer, [{border,4}]),

    wxSizer:add(Column3, MaxLearnedSizer, [{border,4},{flag,?wxDOWN}]),
    wxSizer:add(Column3, MaxLearnedFactorSizer, [{border,4},{flag,?wxDOWN}]),
    wxSizer:add(Column3, MaxLearnedIncSizer, [{border,4},{flag,?wxDOWN}]),
    wxSizer:add(Column3, RestartCounterSizer, [{border,4},{flag,?wxDOWN}]),
    wxSizer:add(Column3, RestartIntervalSizer, [{border,4}]),

    {Backjump, 
     #backjump {
	minimize = Minimize,
	iorder   = IOrder,
	stumble  = Stumble,
	olle     = Olle,
	stumble_olle = StumbleAndOlle,
	max_conflicts = MaxConflicts,
	max_learned = MaxLearned,
	max_learned_factor = MaxLearnedFactor,
	max_learned_inc = MaxLearnedInc,
%%	keep_factor = KeepFactors,
%%	min_keep_clauses = MinKeepClauses,
	restart_counter = RestartCounter,
	restart_interval = RestartInterval
       }}.

varpNumber(Parent, Min, Max, Label, _ToolTip) ->
    Sizer = wxStaticBoxSizer:new(?wxVERTICAL, Parent,
				 [{label, Label}]),
    Entry = wxTextCtrl:new(Parent, 1, [{value, ""},
				       {style, ?wxDEFAULT}]), 
    wxSizer:add(Sizer, Entry, [{border,4},{flag,?wxALL}]),
    {Entry, Sizer}.

varpSpinCtrl(Parent, Min, Max, Label, ToolTip) ->
    Sizer = wxStaticBoxSizer:new(?wxVERTICAL, Parent, 
				 [{label, Label}]),
    Entry = wxSpinCtrl:new(Parent, []),
    wxSpinCtrl:setRange(Entry, Min, Max),
    wxSpinCtrl:setToolTip(Entry, ToolTip),
    wxSizer:add(Sizer,Entry, [{border,4},{flag,?wxALL}]),
    {Entry, Sizer}.
    

-record(s, 
	{
	 window,
	 settings
	}).
	
test() ->
    test(wx:new()).

test(Wx) ->
    Window = wxFrame:new(Wx, -1, "Settings", [{size, {800,600}}]),
    Path = code:priv_dir(varp),
    wxFrame:setIcon(Window,  wxIcon:new(filename:join(Path,"varp.png"),
					[{type, ?wxBITMAP_TYPE_PNG}])),
    wxFrame:createStatusBar(Window,[]),
    ok = wxFrame:connect(Window, close_window, [{skip,false}]),
    Settings = setup(Window),
    S = #s { window = Window,
	     settings = Settings },
    wxWindow:show(S#s.window),
    main_loop(S).

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
	    wxFrame:destroy(S#s.window),
	    {stop, ok, S};

        _Msg = #wx{} ->
            ?dbg("Got ~p ~n", [_Msg]),
	    {noreply, S}
    end.
