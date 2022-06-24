#!/usr/bin/env python3
import argparse
import logging

from SEtaac import Project

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("SEtaac")


def main(args):
    p = Project(target_dir=args.target)

    dot = "digraph g {\n"
    dot += "splines=ortho;\n"
    dot += "node[fontname=\"courier\"];\n"
    for block_id, block in p.block_at.items():
        label = []
        if block_id in p.function_at:
            visibility = "public" if block.function.public else "private"
            color = "blue" if block.function.public else "red"
            label.append(f"{visibility}_func_name={block.function.name}")
        else:
            color = "black"

        label.append(f"block_addr: {block_id}")

        for stmt in block.statements:
            label.append(f"{stmt.stmt_ident}: {stmt}")

        label = "\n".join(label)
        dot += f"\"{block_id}\" [shape=box, color={color}, \nlabel=\"{label}\"];\n\n"

    dot += "\n"

    for function_id, function in p.function_at.items():
        for a, b in function.cfg.graph.edges:
            dot += f"\"{a.ident}\" -> \"{b.ident}\";\n"

    dot += "}"

    print(dot)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("target", type=str, action="store", help="Path to Gigahorse output folder")
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug output")

    args = parser.parse_args()

    # setup logging
    if args.debug:
        log.setLevel("DEBUG")
    else:
        log.setLevel("INFO")

    main(args)
