def gen_exec_id():
    if "xid" not in gen_exec_id.__dict__:
        gen_exec_id.xid = 0
    else:
        gen_exec_id.xid += 1
    return gen_exec_id.xid


class UUID(object):
    def gen_uuid(self):
        if "uuid" not in self.__dict__:
            self.uuid = 0
        else:
            self.uuid += 1
        return self.uuid
