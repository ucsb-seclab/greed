def gen_exec_id():
    if "xid" not in gen_exec_id.__dict__:
        gen_exec_id.xid = 0
    else:
        gen_exec_id.xid += 1
    return gen_exec_id.xid


def gen_uuid():
    if "uuid" not in gen_uuid.__dict__:
        gen_uuid.uuid = 0
    else:
        gen_uuid.uuid += 1
    return gen_uuid.uuid
