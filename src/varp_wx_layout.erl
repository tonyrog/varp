%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2020, Tony Rogvall
%%% @doc
%%%    Generate wx layout from data spec
%%% @end
%%% Created :  5 Jan 2020 by Tony Rogvall <tony@rogvall.se>

-module(varp_wx_layout).

-include_lib("wx/include/wx.hrl").

-export([create/2, create/3]).
-export([handle_sync_event/2]).
-compile(export_all).

%% Create widgets and return toplevel widget and a name map
create(Parent, Root) ->
    create(Parent, Root, #{}).
    
create(Parent, {radiobox,Param,Choices}, NameMap) ->
    {Items,Enums} = choices(Choices),
    W = wxRadioBox:new(Parent, maps:get(id, Param, ?wxID_ANY),
		       maps:get(label, Param, ""),
		       maps:get(position, Param, ?wxDefaultPosition),
		       maps:get(size, Param, ?wxDefaultSize),
		       Items,
		       get_options(Param)),
    case maps:get(value, Param, none) of
	none -> ok;
	Value when is_integer(Value), Value >= 0 ->
	    wxRadioBox:setSelection(W, Value)
    end,
    {W,add_name(Param, W, {enum,Enums}, NameMap)};
create(Parent, {checkbox,Param}, NameMap) ->
    W = wxCheckBox:new(Parent,
		       maps:get(id, Param, ?wxID_ANY),
		       maps:get(label, Param, ""),
		       get_options(Param)),
    {W,add_name(Param, W, boolean, NameMap)};

create(Parent, {checkbox3,Param}, NameMap) ->
    W = wxCheckBox:new(Parent,
		       maps:get(id, Param, ?wxID_ANY),
		       maps:get(label, Param, ""),
		       get_options(Param) ++
			   [{style, ?wxCHK_3STATE bor
				 ?wxCHK_ALLOW_3RD_STATE_FOR_USER}]),
    Enums = [{?wxCHK_UNDETERMINED,undefined},
	     {?wxCHK_CHECKED,true},
	     {?wxCHK_UNCHECKED,false}],
    Value = maps:get(value, Param, none),
    case lists:keyfind(Value, 1, Enums) of
	false -> ok;
	{Chk,_Enum} -> wxCheckBox:set3StateValue(W, Chk)
    end,
    {W,add_name(Param, W, {enum,Enums}, NameMap)};
create(Parent, {radiobutton,Param}, NameMap) ->
    W = wxRadioButton:new(Parent,
			  maps:get(id, Param, ?wxID_ANY),
			  maps:get(label, Param, ""),
			  get_options(Param)),
    {W,add_name(Param, W, boolean, NameMap)};
create(Parent, {textctrl, Param}, NameMap) ->
    Type = maps:get(type, Param, string),
    W = wxTextCtrl:new(Parent, maps:get(id, Param, ?wxID_ANY),
		       get_options(Param)),
    connect(Param, W),
    {W,add_name(Param, W, Type, NameMap)};
create(Parent, {spinctrl, Param}, NameMap) ->
    W = wxSpinCtrl:new(Parent, []),
    Min = maps:get(min, Param, 0),
    Max = maps:get(max, Param, Min+1),
    wxSpinCtrl:setRange(W, Min, Max),
%%    {Wt,Ht,_,_} = wxSpinCtrl:getTextExtent(W,integer_to_list(Max)),
%%    io:format("MaxSize = ~p\n", [{Wt,Ht}]),
%%    wxSpinCtrl:setSize(W, {Wt,Ht}),
    wxSpinCtrl:setToolTip(W, maps:get(tooltip, Param, "")),
    %% fixme declare range
    {W,add_name(Param, W, integer, NameMap)};
create(Parent, {listbox, Param}, NameMap) ->
    Choices = maps:get(choices, Param, ?wxID_ANY),
    {List,Enums} = choices(Choices),
    %% use {style wxLB_MULTIPLE|?wxLB_SINGLE}
    %% options choices
    W = wxListBox:new(Parent,
		      maps:get(id, Param, ?wxID_ANY),
		      get_options(Param) ++ [{choices,List}]),
    wxListBox:setToolTip(W, maps:get(tooltip, Param, "")),
    {W,add_name(Param, W, {enum,Enums}, NameMap)};
create(Parent, {choice, Param}, NameMap) ->
    Choices = maps:get(choices, Param, ?wxID_ANY),
    {List,Enums} = choices(Choices),
    W = wxChoice:new(Parent, maps:get(id, Param, ?wxID_ANY),
		     get_options(Param) ++ [{choices,List}]),
    wxChoice:setSelection(W, maps:get(value,Param,0)),
    wxChoice:setToolTip(W, maps:get(tooltip, Param, "")),
    {W,add_name(Param, W, {enum,Enums}, NameMap)};
create(Parent, {combobox, Param}, NameMap) ->
    Choices = maps:get(choices, Param, ?wxID_ANY),
    {List,Enums} = choices(Choices),
    W = wxComboBox:new(Parent, maps:get(id, Param, ?wxID_ANY),
		       get_options(Param) ++ [{choices,List}]),
    wxComboBox:setToolTip(W, maps:get(tooltip, Param, "")),
    {W,add_name(Param, W, {enum,Enums}, NameMap)};
create(Parent, {slider, Param}, NameMap) ->
    Min0 = maps:get(min, Param, 0),
    Max0 = maps:get(max, Param, 100),
    Min  = min(Min0, Max0),
    Max  = max(Min0, Max0),
    Value = clamp(maps:get(value, Param, 0), Min, Max),
    W = wxSlider:new(Parent,  maps:get(id, Param, ?wxID_ANY),
		     Value, Min, Max,
		     get_options(Param)),
    %% fixme add range?
    {W,add_name(Param, W, integer, NameMap)};
    
%% Box wrapping
create(Parent,{number,Param},NameMap) ->
    TextFun =
	fun(#wx{obj=Widget,event=#wxKey{keyCode=Key}},Ref) ->
		case number_filter(Widget, [Key]) of
		    true ->
			wxEvent:skip(Ref),
			ok;
		    false ->
			ok
		end
	end,
    Layout = 
	{vertical,#{ label=>maps:get(label,Param,"") },
	 [
	  {textctrl,#{ type => number,
			options => [{value,maps:get(value,Param,0)},
				    {style,
				     maps:get(style,Param,default)}
				   ],
			name => maps:get(name,Param,undefined),
			connect => [{key_down,{nospawn,TextFun}}]}}
	 ]},
    create(Parent,Layout,NameMap);
create(Parent,{spin,Param},NameMap) ->
    Layout = {vertical,#{ label => maps:get(label,Param,"") },
	      [
	       {spinctrl,Param} 
	      ]},
    create(Parent, Layout, NameMap);
create(Parent, {vertical,Param,Items}, NameMap) ->
    Orient = ?wxVERTICAL,
    Sizer = case maps:get(label,Param,undefined) of
		undefined ->
		    wxBoxSizer:new(Orient);
		Label ->
		    wxStaticBoxSizer:new(Orient,Parent,[{label,Label}])
	    end,
    {_Children,NameMap1} = create_list(Parent, Sizer, Orient, Items, NameMap),
    {Sizer,NameMap1};
    
create(Parent, {horizontal,Param,Items}, NameMap) ->
    Orient = ?wxHORIZONTAL,
    Sizer = case maps:get(label, Param, undefined) of
		undefined ->
		    wxBoxSizer:new(Orient);
		Label ->
		    wxStaticBoxSizer:new(Orient,Parent,[{label,Label}])
	    end,
    {_Children,NameMap1} = create_list(Parent, Sizer, Orient, Items, NameMap),
    {Sizer,NameMap1}.

%% FIXME add proportion and expand!!!!

create_list(Parent, Sizer, Orient, ItemList, NameMap) ->
    create_list(Parent, Sizer, Orient, ItemList, NameMap, {0,0,0}, []).

create_list(Parent, Sizer, Orient, [{space,Space}|ItemList], 
	    NameMap, {Space0,Prop,Expand}, Acc) ->
    Flags = {Space0+Space, Prop, Expand},
    create_list(Parent, Sizer, Orient, ItemList, NameMap, Flags, Acc);
create_list(Parent, Sizer, Orient, [Prop|ItemList], 
	    NameMap, {Space,_Prop0,Expand}, Acc) when is_integer(Prop) ->
    Flags = {Space, Prop, Expand},
    create_list(Parent, Sizer, Orient, ItemList, NameMap, Flags, Acc);
create_list(Parent, Sizer, Orient, [expand|ItemList], 
	    NameMap, {Space,Prop,_Expand}, Acc) ->
    Flags = {Space, Prop, ?wxEXPAND},
    create_list(Parent, Sizer, Orient, ItemList, NameMap, Flags, Acc);

create_list(Parent, Sizer, Orient, [Item|ItemList], NameMap, 
	    {Space,Prop,Flag}, Acc) ->
    {W,NameMap1} = create(Parent, Item, NameMap),
    Opts = 
	if Space > 0, Orient =:= ?wxVERTICAL ->
		[{proportion,Prop},{flag,?wxUP bor Flag},{border,Space}];
	   Space > 0, Orient =:= ?wxHORIZONTAL ->
		[{proportion,Prop},{flag,?wxLEFT bor Flag},{border,Space}];
	   Flag =/= 0 ->
		[{proportion,Prop},{flag,Flag}];
	   Prop > 0 ->
		[{proportion,Prop}];
	   true ->
		[]
	end,
    wxSizer:add(Sizer, W, Opts),
    create_list(Parent, Sizer, Orient, ItemList, NameMap1, 
		{0,0,0}, [W|Acc]);
create_list(_Parent, _Sizer, _Orient, [], NameMap, _Space, Acc) ->
    {lists:reverse(Acc), NameMap}.

choices(List) ->
    choices(List, 0, [], []).

choices([{Name,Enum} | Choices], I, Names, Enums) ->
    choices(Choices, I+1, [Name|Names], [{I,Enum}|Enums]);
choices([Name | Choices], I, Names, Enums) ->
    choices(Choices, I+1, [Name|Names], [{I,I}|Enums]);
choices([], _I, Names, Enums) ->
    {lists:reverse(Names), lists:reverse(Enums)}.

set_enums(Widget, Enums) ->
    lists:foreach(
      fun({I,Enum}) ->
	      wxControlWithItems:setClientData(Widget,I,Enum)
      end, Enums).

add_name(Param, Widget, Type, NameMap) ->
    case maps:get(name, Param, undefined) of
	undefined -> NameMap;
	Name ->
	    NameMap#{ Name => {Widget,Type} }
    end.

connect(Param, Widget) ->
    Class = wx:getObjectType(Widget),
    case maps:get(connect, Param, []) of
	[] -> ok;
	HandlerList ->
	    lists:foreach(fun(Type) when is_atom(Type) ->
				  Class:connect(Widget, Type);
			     ({Type,Fun}) when is_atom(Type),
					       is_function(Fun) ->
				  Class:connect(Widget, Type, 
						[{callback,Fun}]);
			     ({Type,{nospawn,Fun}}) when is_atom(Type),
							 is_function(Fun) ->
				  Class:connect(Widget, Type, 
						[{callback,{nospawn,Fun}}]);
			     ({Type,skip}) when is_atom(Type) ->
				  Class:connect(Widget, Type, 
						[{skip,true}]);
			     ({Type,sync}) when is_atom(Type) ->
				  io:format("CONNECT SYNC\n"),
				  Class:connect(Widget, Type, 
						[callback])
			  end, HandlerList)
    end.

handle_sync_event(Wx, _State) ->
    io:format(" ~s: handle_sync_event: ~w\n", [?MODULE, Wx]),
    ok.

number_filter(Widget, Codes) ->
    Pos  = wxTextCtrl:getInsertionPoint(Widget),
    Text = wxTextCtrl:getValue(Widget),
    %% io:format("Pos=~w, Codes=~w, Text=~w\n", [Pos, Codes, Text]),
    case text_edit(Pos, Text, Codes) of
	{true, Text1} ->
	    %% io:format("Text1=~w\n", [Text1]),
	    is_partial_number(Text1);
	false ->
	    false
    end.

%% partial numbers:
%% + | - | 3.
%% 0   0   3.0

is_partial_number([$-|Cs]) -> part_d0(Cs);
is_partial_number([$+|Cs]) -> part_d0(Cs);
is_partial_number(Cs) -> part_d0(Cs).

%% \d+(\.)
part_d0([C|Cs]) when C >= $0, C =< $9 -> part_d(Cs);
part_d0([]) -> true;  %% partial ok
part_d0(_) -> false.

part_d([C|Cs]) when C >= $0, C =< $9 -> part_d(Cs);
part_d([$.|Cs]) -> part_f(Cs);
part_d([]) -> true;  %% partial ok
part_d(_) -> false.
%% \d*
part_f([C|Cs]) when C >= $0, C =< $9 -> part_f(Cs);
part_f([]) -> true;   %% partial ok
part_f(_) -> false.


text_edit(Codes) ->
    text_fwd(0, [], [],  Codes).

text_edit(Text, Codes) ->
    text_fwd(0, [], Text, Codes).

text_edit(Pos, Text, Codes) ->
    text_fwd(Pos, [], Text, Codes).

text_fwd(0, Bs, As, Codes) ->
    text_ed(Codes, Bs, As);
text_fwd(I, Bs, [A|As], Codes) ->
    text_fwd(I-1, [A|Bs], As, Codes).
%%text_fdw(_, [], As, Codes) ->
%%    text_ed(Code, Bs, As).

text_ed(Codes) ->
    text_ed(Codes, [], []).

text_ed([?WXK_BACK|Cs], [_|Bs], As) ->
    text_ed(Cs, Bs, As);
text_ed([?WXK_DELETE|Cs], Bs, [_|As]) ->
    text_ed(Cs, Bs, As);
text_ed([?WXK_LEFT|Cs], [B|Bs], As) ->
    text_ed(Cs, Bs, [B|As]);
text_ed([?WXK_RIGHT|Cs], Bs, [A|As]) ->
    text_edit(Cs, [A|Bs], As);
text_ed([C|Cs], Bs, As) ->
    text_ed(Cs, [C|Bs], As);
text_ed([], Bs, As) ->
    %% io:format("Bs=~w, As=~w\n", [Bs,As]),
    {true, lists:reverse(Bs,As)};
text_ed(_, _Bs, _As) ->
    false.


clamp(I, Min, Max) ->
    min(max(I, Min), Max).

%% We want to be able to have a readable externa format
%% so here we allow style and flag ... as enums

options([{style,Style}|Options]) ->
    [{style, style(Style)} | options(Options)];
options([{flag,Flag}|Options]) ->
    [{flag,flag(Flag)} | options(Options)];
options([KV|Options]) ->
    [KV|options(Options)];
options([]) ->
    [].

get_options(Param) ->
    options(maps:get(options, Param, [])).


style() ->
    #{
      default => ?wxDEFAULT,
      vertical => ?wxVERTICAL,
      horizontal => ?wxHORIZONTAL,
      rb_group =>   ?wxRB_GROUP,
      bk_default => ?wxBK_DEFAULT,
      bk_align_mask => ?wxBK_ALIGN_MASK,
      bk_top => ?wxBK_TOP,
      bk_bottom => ?wxBK_BOTTOM,
      bk_left => ?wxBK_LEFT,
      bk_right => ?wxBK_RIGHT,
      bk_multiline => ?wxNB_MULTILINE,
%% align
      align_center_horizontal => ?wxALIGN_CENTER_HORIZONTAL,
      align_not => ?wxALIGN_NOT,
      align_top => ?wxALIGN_TOP,
      align_right => ?wxALIGN_RIGHT,
      align_bottom => ?wxALIGN_BOTTOM,
      align_center_vertival => ?wxALIGN_CENTER_VERTICAL,
      align_center => ?wxALIGN_CENTER,
%% frame
      default_frame_style => ?wxDEFAULT_FRAME_STYLE,
      frame_float_on_parent => ?wxFRAME_FLOAT_ON_PARENT,
%% border
      border_simple => ?wxBORDER_SIMPLE,
%% slider
      sl_horizontal => ?wxSL_HORIZONTAL,
      sl_vertical => ?wxSL_VERTICAL,
      sl_labels => ?wxSL_LABELS,
      sl_inverse => ?wxSL_INVERSE
      }.

style(F) when is_atom(F) -> maps:get(F, style());
style(F) when is_integer(F) -> F;
style(F) when is_list(F) -> enum_list(F, 0, style()).

flag() ->
    #{
      expand => ?wxEXPAND,
      up => ?wxUP,
      down => ?wxDOWN,
      left => ?wxLEFT,
      right => ?wxRIGHT
     }.

flag(F) when is_atom(F) -> maps:get(F, flag());
flag(F) when is_integer(F) -> F;
flag(F) when is_list(F) -> enum_list(F, 0, flag()).

enum_list([E|Es], Enum, Map) ->
    Value = if is_atom(E) -> maps:get(E, Map);
	       is_integer(E) -> E
	    end,
    enum_list(Es, Value bor Enum, Map);
enum_list([], Enum, _Map) ->
    Enum.
