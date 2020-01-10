-ifndef(__VARP_WX_HRL__).
-define(__VARP_WX_HRL__, true).

-record(wi,
	{
	 type :: boolean | integer | 
		 decimal | string  | {enum,[{integer(),atom()}]},
	 min  :: term(),
	 max  :: term(),
	 default :: term()
	}).

-endif.

