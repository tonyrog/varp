%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2011, Tony Rogvall
%%% @doc
%%%    Record definition of parse elements
%%% @end
%%% Created : 10 Jan 2011 by Tony Rogvall <tony@rogvall.se>

-ifndef(__VARP_BIC_HRL__).
-define(__VARP_BIC_HRL__, true).

-record(cid,
	{ 
	  line,
	  name
	 }).

-record(ctypeid,
	{
	  line,
	  name
	 }).

-record(cconst,
	{
	  line :: integer(),
	  base :: 2 | 8 | 10 | 16 | char | float | string,
	  value :: string()
	}).
	  
-record(cunary,
	{
	  line :: integer(),
	  op   :: atom(),
	  arg
	 }).

-record(cbinary,
	{
	  line :: integer(),
	  op   :: atom(),
	  arg1,
	  arg2
	 }).

-record(ccall,
	{
	  line :: integer(),
	  func,
	  args
	 }).
	
%%  cond ? then : else FIXME? GNU:  cond ? then
-record(cifexpr,
	{
	  line :: integer(),
	  test,
	  then,
	  else
	 }).

-record(cassign,
	{
	  line :: integer(),
	  op,
	  lhs,
	  rhs
	 }).

%% Function declaration
-record(cfunction,
	{
	  line :: integer(),       %% line number
	  name,
	  storage,    %% list of specifiers & return type
	  type,       %% {fn,..} function argument type with formal params
	  params,     %% list of (old style) parameters [#decl]
	  body        %% function body
	 }).

%% variable & element declarations
-record(cdecl,
	{
	  line :: integer(),    %% line number
	  name,    %% optional identifier
	  type=[], %% type (specifier list)
	  size,    %% optional constant bit field size
	  value    %% init value assignment-expr | [assignment-expr]
	}).

%% Specialize declaration - simplify processing a bit
-record(ctypedef,
	{
	  line :: integer(),    %% line number
	  name,    %% name of type defined
	  type=[], %% type spec
	  size,    %% optional constant bit field size
	  value    %%  init value (error if present)
	}).

-record(cstruct,
	{
	  line :: integer(),
	  name,
	  elems
	 }).

-record(cunion,
	{
	  line :: integer(),
	  name,
	  elems
	 }).

-record(cenum,
	{
	  line :: integer(),
	  name,   %% string() | undefined
	  elems   %% [{id,value|undefined}]
	 }).

-record(cfor,
	{
	  line :: integer(),    %% line number
	  init,
	  test,
	  update,
	  body 
	 }).

-record(cwhile,
	{
	  line :: integer(),    %% line number
	  test,
	  body 
	 }).

-record(cdo,
	{
	  line :: integer(),    %% line number
	  body,
	  test
	 }).

-record(cif,
	  {
	  line :: integer(),
	  test,
	  then,
	  else
	  }).

-record(cswitch,
	{
	  line :: integer(),
	  expr,
	  body 
	 }).

-record(ccase,
	{
	  line :: integer(),
	  expr,
	  code
	 }).

-record(cdefault,
	{
	  line :: integer(),
	  code
	 }).

-record(clabel,
	{
	  line :: integer(),
	  name,
	  code
	 }).

	
-record(cgoto,
	{
	  line :: integer(),
	  label
	 }).

-record(ccontinue,
	{
	  line :: integer()
	 }).

-record(cbreak,
	{
	  line :: integer()
	 }).
	
-record(creturn,
	{
	  line :: integer(),
	  expr
	 }).

-record(cempty,
	{
	  line :: integer()
	}).

%% special  a..b  range
-record(crange,
	{
	  line :: integer(),
	  from,
	  to
	}).

-endif.
