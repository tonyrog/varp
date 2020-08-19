import lark

varp_parser = lark.Lark.open('varp.lark',
                             rel_to=__file__,
                             parser="lalr",
                             propagate_positions=True)

def text(data):
    return varp_parser.parse(data)

def file(name):
    f = open(name)
    text = f.read()
    print(text)
    f.close()
    return varp_parser.parse(text)

