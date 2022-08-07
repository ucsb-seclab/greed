


# Temporary, Yices specific.
def get_array_base(self,array):
    if hasattr(array, "children"):
        for c in array.children:
            if hasattr(c, "operator"):
                if c.operator == "store":
                    self.get_array_base(c)
                elif c.operator == "array":
                    print(c.name)

