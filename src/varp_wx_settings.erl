%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    Show settings dialog
%%% @end
%%% Created : 17 Dec 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_wx_settings).

-include_lib("wx/include/wx.hrl").

-export([load/0]).
-export([save/1]).
-export([create/2]).
-export([get_values/2]).
-export([set_values/2]).
-export([get_value/1]).
-export([set_value/2]).
-export([set_attribute/3, set_attribute/4]).
-export([settings_filename/0]).
-export([home_directory/0]).

%% -define(DEBUG, true).
%% -compile(export_all).

-include("varp.hrl").
-include("varp_wx.hrl").

load() ->
    case file:consult(settings_filename()) of
	{ok,Settings} ->
	    load_settings(Settings);
	{error,enoent} ->
	    #{}
    end.

save(Values) ->
    Profiles = save_settings(Values),
    Data = lists:map(
	     fun(Pi) ->
		     io_lib:format("~p.\n", [Pi])
	     end, Profiles),
    file:write_file(settings_filename(), Data).

settings_filename() ->
    filename:join(home_directory(), ".varp.settings").

home_directory() ->
    case os:type() of
	{win32,_} ->
	    os:getenv("USERPROFILE");
	_ ->
	    os:getenv("HOME")
    end.

%% FIXME: Better name ???? Load settings from erlang term representation
load_settings(Settings) ->
    load_ordered_(Settings, 1, [], #{}).

%% FIXME: Better name Save settings map to term representation
save_settings(ValueMap) ->
    maps:fold(fun(K, V, Acc) -> insert_kv(K,V,Acc) end, [], ValueMap).

insert_kv([K,I|Ks], V, Acc) when is_atom(K), is_integer(I) ->
    insert_ordered(I, K, Ks, V, Acc);
insert_kv([K|Ks], V, Acc) when is_atom(K) ->
    insert_unordered(K, Ks, V, Acc);
insert_kv([], Value, []) ->
    Value.

insert_unordered(K, Ks, V, [{K,W}|Acc]) ->
    [{K, insert_kv(Ks, V, W)} | Acc];
insert_unordered(K, Ks, V, [E|Acc]) ->
    [E | insert_unordered(K, Ks, V, Acc)];
insert_unordered(K, Ks, V, []) ->
    [{K, insert_kv(Ks, V, [])}].

insert_ordered(1, K, Ks, V, [{K,W}|Acc]) ->
    [{K, insert_kv(Ks, V, W)} | Acc];
insert_ordered(1, K, Ks, V, Acc) ->
    [{K, insert_kv(Ks, V, [])} | Acc];
insert_ordered(I, K, Ks, V, [E={K,_W}|Acc]) when I > 1 ->
    [E | insert_ordered(I-1, K, Ks, V, Acc)];
insert_ordered(I, K, Ks, V, Acc) when I > 1 ->
    [{K,[]} | insert_ordered(I-1, K, Ks, V, Acc)].

%% load ordered items
load_ordered_([{Key,Value}|List], I, Parent, Map) ->
    case is_value(Value) of
	true ->
	    load_ordered_(List, I+1, Parent, Map#{ Parent++[Key,I] => Value });
	false ->
	    case is_unordered(Value) of
		true ->
		    Map1 = load_unordered_(Value, Parent++[Key,I], Map),
		    load_ordered_(List, I+1, Parent, Map1);
		false ->
		    case is_ordered(Value) of
			true ->
			    Map1 = load_ordered_(Value,1,Parent++[Key,I],Map),
			    load_ordered_(List, I+1, Parent, Map1);
			false ->
			    error({item_list_error,Key,Value})
		    end
	    end
    end;
load_ordered_([], _I, _Name, Map) ->
    Map.

%% load unordered items
load_unordered_([{Key,Value}|List], Parent, Map) ->
    case is_value(Value) of
	true ->
	    load_unordered_(List, Parent, Map#{ Parent++[Key] => Value });
	false ->
	    case is_unordered(Value) of
		true ->
		    Map1 = load_unordered_(Value, Parent++[Key], Map),
		    load_unordered_(List, Parent, Map1);
		false ->
		    case is_ordered(Value) of
			true ->
			    Map1 = load_ordered_(Value,1,Parent++[Key],Map),
			    load_unordered_(List, Parent, Map1);
			false ->
			    error({item_list_error,Key,Value})
		    end
	    end
    end;
load_unordered_([], _Parent, Map) ->
    Map.

is_value(Value) when is_number(Value) -> true;
is_value(Value) when is_atom(Value) -> true;
is_value(Value) when is_binary(Value) -> true;
is_value(Value) when is_list(Value) -> 
    try list_to_binary(Value) of
	_String -> true
    catch
	error:_ -> false %% array of something
    end;
is_value(_Value) ->
    false.

%% ordered list: all items have the same tags
%% [{x,a},{x,b},{x,c}] gives map [x,1] => a, [x,2] => b, [x,3] => c
is_ordered(Value) when is_list(Value) ->
    L = [X || {X,_} <- Value, is_atom(X)],
    if length(L) =:= length(Value) ->
	    case lists:usort(L) of
		[_] -> true;
		_ -> false
	    end;
       true ->
	    false
    end;
is_ordered(_) ->
    false.

%% unordered list: all items must have different tags
%% [{x,a}, {y,b}, {z,d}] gives map [x] => a, [y] => b, [z] => d
is_unordered(Value) when is_list(Value) ->
    L = [X || {X,_} <- Value, is_atom(X)],
    length(lists:usort(L)) =:= length(Value);
is_unordered(_) ->
    false.

%% FIXME: arrange items in ordered and unordered groups
%% [{x,a},{x,b}, {y,1}, {z,2}, {x,c}] could give
%% [x,1] => a, [x,2] => b, [x,3] => c, [y] => 1, [z] => 2
%%
-define(DEF, {pos,?wxDefaultPosition},{size,?wxDefaultSize}).

create(Parent, ValueMap) ->
    Panel = wxPanel:new(Parent, [?DEF]),
    %% Setup sizers
    MainSizer = wxStaticBoxSizer:new(?wxVERTICAL, Panel, 
				     [{label, "Settings"}]),
    Notebook = wxNotebook:new(Panel, 1, 
			      [{pos,?wxDefaultPosition},
			       {size,?wxDefaultSize},
			       {style, ?wxBK_DEFAULT%,
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

    NameMap = lists:foldl(
		fun(I, Ni) ->
			add_page(Notebook,I,Ni)
		end, #{}, lists:seq(1,10)),

    set_values(NameMap, ValueMap),

    Buttons = wxStaticBoxSizer:new(?wxHORIZONTAL,Panel,[]),
    Apply = wxButton:new(Panel, ?wxID_ANY, [{label,"Apply"},?DEF]),
    wxButton:connect(Apply, command_button_clicked),
    wxButton:enable(Apply),

    Cancel = wxButton:new(Panel, ?wxID_ANY, [{label,"Cancel"},?DEF]),
    wxButton:connect(Cancel, command_button_clicked),
    wxButton:enable(Cancel),
    wxSizer:add(Buttons, Apply),
    wxSizer:add(Buttons, Cancel),
    wxSizer:add(MainSizer, Buttons),

    wxPanel:setSizer(Panel, MainSizer),    

    {Panel,Notebook,Apply,Cancel,NameMap}.

add_page(Notebook,I,NameMap) ->
    Panel = wxPanel:new(Notebook, []),
    Layout = varp_layout(I),
    {Config,NameMap1} = varp_wx_layout:create(Panel, Layout, NameMap),
    wxPanel:setSizer(Panel, Config),
    wxNotebook:addPage(Notebook, Panel, integer_to_list(I), []),
    NameMap1.

%% setup current widget values!
set_values(NameMap, Values) ->
    maps:fold(
      fun(Name, {Widget,WI}, _Acc) ->
	      try maps:get(Name, Values) of
		  Value0 ->
		      ?dbg("import ~w/~w ~w\n", [Name, WI, Value0]),
		      try value_import(Value0, WI#wi.type) of
			  Value ->
			      set_value(Widget, Value)
		      catch
			  error:_ ->
			      io:format("Bad type: ~w/~w = ~p\n", 
					[Name,WI#wi.type,Value0]),
			      error
		      end
	      catch
		  error:_ ->
		      %% io:format("New Key ~w\n", [Name]),
		      ok
	      end
      end, ok, NameMap).

%% read all the current values from the widget map
get_values(NameMap, ValueMap) ->
    maps:fold(
      fun(Name, {Widget,WI}, Map) ->
	      Value0 = get_value(Widget),
	      ?dbg("export ~w/~w ~w\n", [Name, WI, Value0]),
	      Value = value_export(Value0, WI#wi.type),
	      Map#{ Name => Value }
      end, ValueMap, NameMap).

%%
%% Convert from varp value info "widget" value
%%
value_import(Enum, {enum,Enums}) ->
    case lists:keyfind(Enum, 2, Enums) of
	false -> 
	    ?warn("enum ~w not among enums ~p\n", [Enum, Enums]),
	    0;
	E ->
	    list_index(E, Enums)-1
    end;
value_import(Value, string) when is_float(Value) ->
    io_lib_format:fwrite_g(Value);
value_import(Value, string) when is_integer(Value) ->
    integer_to_list(Value);
value_import(Value, string) when is_list(Value) ->
    Value;
value_import(Value, boolean) when is_boolean(Value) ->
    Value;
value_import(Value, boolean) when Value =:= 0 ->
    false;
value_import(Value, boolean) when Value =:= 1 ->
    true;
value_import(Value, integer) when is_integer(Value) ->
    Value;
%% number is represented as text by wxTextCtrl
value_import(Value, decimal) when is_float(Value) ->
    io_lib_format:fwrite_g(Value);
value_import(Value, decimal) when is_integer(Value) ->
    integer_to_list(Value);
value_import("", decimal) ->
    "0".

list_index(E, List) ->
    index_(E, List, 1).

index_(E, [E|_], I) -> I;
index_(E, [_|L], I) -> index_(E, L, I+1);
index_(_E, [], _) -> 0.
    
%%
%% Convert from "widget" value to varp value
%%
value_export(Value, {enum,Enums}) ->
    %% assume? that Value is choice index 
    try lists:nth(Value+1, Enums) of
	{_Name,Enum} -> Enum
    catch
	error:_ ->
	    0
    end;
value_export(Value, string) when is_list(Value) ->
    Value;
value_export(Value, string) when is_atom(Value) ->
    atom_to_list(Value);
value_export(Value, boolean) when is_boolean(Value) ->
    Value;
value_export(Value, integer) when is_integer(Value) ->
    Value;
value_export(Value, decimal) when is_number(Value) ->
    Value;
%% number is represented as text by wxTextCtrl
value_export("", decimal) ->
    %% default?
    0;
value_export(Text, decimal) ->
    try list_to_float(Text) of
	Value -> Value
    catch
	error:_ ->
	    list_to_integer(Text)
    end.

%%
%% setup setting  layout given profile number
%% Maybe put in resource file!
%%
-define(HSPACE, 10).
-define(VSPACE, 4).

varp_layout(I) when is_integer(I) ->
    Backtrack = {radiobox,
		 #{ label => "Backtrack",
		    name => [profile,I,method],
		    options => [{majorDim,1},{style,vertical}]},
		 [{"Backjump",backjump}, 
		  {"Backtrack",backtrack},
		  {"None",none}]},

    Assoc = {radiobox,
	     #{ label => "Assoc",
		name => [profile,I,options,varp,assoc],
		options => [{majorDim,1},{style,vertical}]},
	     [{"Left",  left},
	      {"Right", right},
	      {"Mid",   balanced}, 
	      {"None",  none}] },

    QType = {radiobox,
	     #{ label => "QType",
		name => [profile,I,options,varp,qtype],
		options => [{majorDim,1},{style,vertical}]},
	     [{"Fifo", fifo},
	      {"Lifo", lifo},
	      {"Recursive",recursive} ]},
    
    Order = {vertical,#{ label => "Order" },
	     [
	      {horizontal,#{},
	       [{checkbox,#{ label => "Ascend",
			     name=> [profile,I,options,order,key1,dir]}},
		{radiobox,
		 #{ name => [profile,I,options,order,key1,sort],
		    options => [{majorDim,1},{style,vertical}]},
		 [{"Deg",degree}, {"Rank",rank},
		  {"User",user}, {"Rand",random}, {"Input",identity},
		  {"Undef",undefined}]}
	       ]},
	      {horizontal,#{},
	       [{checkbox,#{ label => "Ascend",
			     name=> [profile,I,options,order,key1,dir]}},
		{radiobox,
		 #{ name => [profile,I,options,order,key2,sort],
		    options => [{majorDim,1},{style,vertical}]},
		 [{"Deg",degree},{"Rank",rank},
		  {"User",user},{"Rand",random},{"Input",identity},
		  {"Undef",undefined}]}
	       ]}
	     ]},

    Saturate = 
	{vertical,#{ label => "Saturate" },
	 [
	  {horizontal,#{},
	   [{spin, #{ label => "Sequence",
		      name => [profile,I,options,saturate,q],
		      min => 0, max => 100,
		      tooltip =>
			  "Add q consecutive variables during saturation."
		    }},
	    {spin, #{ label => "Random",
		      name => [profile,I,options,saturate,r],
		      min => 0, max => 100,
		      tooltip =>
			  "Add r random variables during saturation."
		    }}
	   ]},
	  {horizontal,#{},
	   [
	    {spin, #{ label => "Laps",
		      name => [profile,I,options,saturate,laps],
		      min => 0, max => 100,
		      tooltip =>
			  "Max saturation lap count"
		    }},
	    {spin, #{ label => "Threshold",
		      name => [profile,I,options,saturate,threshold],
		      min => 0, max => 100,
		      tooltip =>
			  "Threshold for bound variables during saturation"
		      "round."
		    }}
	   ]}
	 ]},
			   
    Backjump = 
	{horizontal, #{ label=>"Backjump" },
	 [
	  {space, ?HSPACE},

	  {vertical, #{},
	   [
	    {radiobox,
	     #{ label => "Minimize",
		name => [profile,I,options,backjump,minimize],
		options => [{majorDim,1},{style,vertical}]},
	     [{"None", none},
	      {"Local", local},
	      {"Recursive", recursive}]},
	    {space, ?VSPACE},
	    {vertical, #{ label => "Max clause length" },
	     [
	      expand,
	      {slider,#{ name => [profile,I,options,backjump,iorder],
			 value => 3,
			 min => 0, max => 100,
			 options => [{style,[sl_horizontal,sl_labels]}]
		       }}
	     ]},
	    {space, ?VSPACE},
	    {spin,#{ label => "Max conflicts", 
		     name => [profile,I,options,backjump,max_conflicts],
		     min => 0, max => 10 }}
	   ]},
	  
	  {space, ?HSPACE},

	  {vertical, #{},
	   [{checkbox,#{ label => "Stumble+Olle", 
			  name=>[profile,I,options,backjump,stumble_olle]}},
	    {space, ?VSPACE},
	    {spin,#{ label => "Stumble",
		     name=>[profile,I,options,backjump,stumble],
		     min => 0, max => 100 }},
	    {space, ?VSPACE},
	    {decimal, #{ label => "Olle", 
			 name=>[profile,I,options,backjump,olle],
			 min => 0.0, max => 100.0 }}
	   ]},

	  {space, ?HSPACE},

	  {vertical, #{},
	   [{spin,#{ label => "Max learned clauses", 
		     name=> [profile,I,options,backjump,max_learned_clause],
		     min => 0, max => 1000000000 }},
	    {space, ?VSPACE},
	    {decimal,#{ label => "Max learned factor",
			name => [profile,I,options,backjump,max_learned_factor],
			default => 0,
			min => 0.0, max => 100.0 }},
	    {space, ?VSPACE},
	    {decimal,#{ label => "Max learned inc",
			name => [profile,I,options,backjump,max_learned_inc],
			default => 0,
			min => 0.0, max => 100.0 }}
	   ]},

	  {space, ?HSPACE},

	  {vertical, #{},
	   [
	    {spin,#{ label => "Restart counter",
		     name => [profile,I,options,backjump,restart_counter],
		     default => 0,
		     min => 0, max => 1000000000 }},
	    {space, ?VSPACE},
	    {decimal,#{ label => "Restart interval",
			name => [profile,I,options,backjump,restart_interval],
			default => 0,
			min => 0.0, max =>  2592000.0 }},  %% 30days
	    {space, ?VSPACE},
	    {decimal,#{ label => "Keep factor",
			name => [profile,I,options,backjump,keep_factor],
			default => 0.5,
			min => 0.0, max => 1.0 }}
	   ]},

	  {space, ?HSPACE},

	  {vertical, #{},
	   [
	    {vertical,#{ label => "Bump" },
	     [
	      {combobox, #{ choices =>
				[{"none", ?BUMP_NONE},
				 {"1", 1},{"2", 2},{"3", 3},{"4", 4},{"5", 5},
				 {"next", ?BUMP_NEXT},
				 {"log2", ?BUMP_LOG2},
				 {"log10", ?BUMP_LOG10},
				 {"rank", ?BUMP_RANK},
				 {"0.3", 0.3},{"0.5", 0.5},{"0.8", 0.8},
				 {"10", 10}, {"15", 15}, {"20", 20}, {"50", 50},
				 {"100", 100}],
			    name => [profile,I,options,backjump,bump]
			  }}
	     ]}
	   ]}
	 ]},

    {vertical,#{},
     [
      {horizontal,#{}, [
			{vertical,#{ label => "Panel name" },
			 [
			  {textctrl,#{ name => [profile,I,name] }}
			 ]},
			{space, ?HSPACE},
			Backtrack, {space,?HSPACE}, Assoc,
			{space,?HSPACE}, QType]},
      {space,?VSPACE},
      {horizontal,#{}, [
			Order, {space,?HSPACE}, Saturate
		       ]},
      {space,?VSPACE},
      Backjump
     ]}.

get_value(Widget) ->
    get_val_(wx:getObjectType(Widget), Widget).

get_val_(wxRadioBox, Widget) ->
    wxRadioBox:getSelection(Widget);
get_val_(wxRadioButton, Widget) ->
    wxRadioButton:getValue(Widget);
get_val_(wxSpinCtrl, Widget) ->
    wxSpinCtrl:getValue(Widget);
get_val_(wxSlider, Widget) ->
    wxSlider:getValue(Widget);
get_val_(wxChoice, Widget) ->
    wxChoice:getSelection(Widget);
get_val_(wxComboBox, Widget) ->
    Sel = wxComboBox:getSelection(Widget),
    %% io:format("wxComboBox getSelection = ~w\n", [Sel]),
    Sel;
get_val_(wxTextCtrl, Widget) ->
    Text = wxTextCtrl:getValue(Widget),
    try list_to_float(Text) of
	Value -> Value
    catch
	error:_ ->
	    try list_to_integer(Text) of
		Value -> Value
	    catch
		error:_ ->
		    Text
	    end
    end;
get_val_(wxCheckBox, Widget) ->
    case wxCheckBox:is3State(Widget) of
	true ->
	    case wxCheckBox:get3StateValue(Widget) of
		?wxCHK_CHECKED -> true;
		?wxCHK_UNCHECKED -> false;
		?wxCHK_UNDETERMINED -> none
	    end;
	false ->
	    wxCheckBox:getValue(Widget)
    end.

    
set_value(Widget, Value) ->
    set_value(wx:getObjectType(Widget), Widget, Value).

set_value(wxRadioBox, Widget, Value) ->
    wxRadioBox:setSelection(Widget, Value);
set_value(wxRadioButton, Widget, Value) ->
    wxRadioButton:setValue(Widget, Value);
set_value(wxSpinCtrl, Widget, Value) ->
    wxSpinCtrl:setValue(Widget, Value);
set_value(wxSlider, Widget, Value) ->
    wxSlider:setValue(Widget, Value);
set_value(wxChoice, Widget, Value) ->
    wxChoice:setSelection(Widget, Value);
set_value(wxComboBox, Widget, Value) ->
    wxComboBox:setSelection(Widget, Value);
set_value(wxTextCtrl, Widget, Value) ->
    Text = if is_float(Value) -> io_lib_format:fwrite_g(Value);
	      is_integer(Value) -> integer_to_list(Value);
	      is_list(Value) -> Value
	   end,
    wxTextCtrl:setValue(Widget, Text);
set_value(wxCheckBox, Widget, Value) ->
    case wxCheckBox:is3State(Widget) of
	true ->
	    Value3 = case Value of
			 true -> ?wxCHK_CHECKED;
			 false -> ?wxCHK_UNCHECKED;
			 none  -> ?wxCHK_UNDETERMINED;
			 _ when is_integer(Value) -> Value
		     end,
	    wxCheckBox:set3StateValue(Widget, Value3);
	false ->
	    wxCheckBox:setValue(Widget, Value)
    end.

%% 
%% Start set/get of various data
%%

set_attribute(Name, Attribute, Value, NameMap) ->
    {Widget,_WI} = maps:get(Name, NameMap),
    set_attribute(Widget, Attribute, Value).

set_attribute(Widget, Attribute, Value) ->
    set_attr_(wx:getObjectType(Widget), Widget, Attribute, Value).

set_attr_(Class, Widget, background_color, Value) ->
    Class:setBackgroundColour(Widget, Value);
set_attr_(Class, Widget, background_style, Value) ->
    %% style_system | style_colour | style_custom
    Class:setBackgroundStyle(Widget, Value);
set_attr_(Class, Widget, foreground_color, Value) ->
    Class:setForegroundColour(Widget, Value);
set_attr_(Class, Widget, transparent, Value) ->
    Class:setTransparent(Widget, Value);
set_attr_(Class, Widget, size, Value) ->
    Class:setSize(Widget, Value);
set_attr_(Class, Widget, help_text, Value) ->
    Class:setHelpText(Widget, Value);
set_attr_(Class, Widget, tooltip, Value) ->
    Class:setToolTip(Widget, Value).
