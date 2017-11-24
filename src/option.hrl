-ifndef(__OPTION_HRL__).
-define(__OPTION_HRL__, true).

-type unsigned_t() :: non_neg_integer().
-type order_t() :: identity | reverse | depth | occure | 
		   depth_occure | occure_depth.

-record(option,
	{
	  value = none ::  boolean() | none,   
	  order = identity :: order_t(),
	  print = false :: boolean()|model|literal,  %% print models
	  partial = false :: boolean(),   %% print partial model (eval/saturate)
	  log   = -1 :: -1 .. 7,
	  max   = 0 :: unsigned_t(),            %% max number of models to find
	  method = collect :: count|collect,    %% model collect|count
	  carry = ignore  :: true|false|ignore, %% ignore carry condition
	  borrow = ignore :: true|false|ignore, %% ignore borrow condition
	  divz   = false  :: true|false|ignore, %% do not accept divide by zero
	  bcp    = false  :: boolean(),         %% do not use equvalence classes
	  saturate = 0 :: unsigned_t(),         %% saturate formula
	  backtrack = true :: boolean(),        %% find models with backtrack
	  threshold = 0 :: unsigned_t(),  %% >i variables changed -> loop again
	  pair = true :: boolean(),       %% saturate pair algoritm	
	  assoc = left :: left|right|middle, %% fold op
	  meta = [],
	  defs = [],
	  decls = [],
	  code = [],
	  backend = vare :: atom()
	}).

-endif.
