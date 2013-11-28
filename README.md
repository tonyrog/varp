Propositional logic library
===========================

The main module is varp

Current options to varp

Key			Value
value			boolean()|none	main formula variable value
print			boolean()	print models when found
method			collect|count	count or collect models
max			unsigned()	max number of models to collect
order			<order>
eval_bcp		boolean()	do not use equivalnce classes
saturate		unsigned()	saturation vector width
pair		        boolean()    test two variables at a time
threshold	        unsigned()   take more rounds in saturation.
carry			boolean()|ignore
borrow			boolean()|ignore
divz			boolean()|ignore
log			<level>


Command line tool

varp [satisfy|falsify|prove] [options] [bindings] [file1.varp ... filen.varp]

options
     --value      true|false|none	(none)
     --print      true|false		(false)
     --method     collect|count		(collect)
     --max        <unsigned>		(0=all)
     --order      <order>		(identity)
     --bcp        true|false		(false)
     --saturate   <unsigned>		(0=eval)
     --pair       true|false		(true)
     --threshold  <unsigned>		(0)
     --carry      true|false|ignore	(ignore)
     --borrow     true|false|ignore	(ignore)
     --divz       true|false|ignore	(false)
     --log        <level>		(none)

bindings 
	 <var> = <value>

order
	identity | 
	reverse | 
	depth|
	occure |
	depth_occure |
	occure_depth |
	<var>*

level
	debug |
	info |
	notice |
	warning |
	error |
	critical |
	alert |
	emergency |
	none
