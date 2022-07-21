def gen_exec_id():
    if "xid" not in gen_exec_id.__dict__:
        gen_exec_id.xid = 0
    else:
        gen_exec_id.xid += 1
    return gen_exec_id.xid


class UUID(object):
    def gen_uuid(self):
        if "uuid" not in self.__class__.__dict__:
            self.__class__.uuid = 0
        else:
            self.__class__.uuid += 1
        return self.__class__.uuid
