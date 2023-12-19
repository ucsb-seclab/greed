import pkgutil
import importlib
import os
import alive_progress

TARGET_FOLDER = "../docs/modules/"
GITHUB_URL = "https://github.com/ucsb-seclab/greed/tree/main"

def list_submodules(package_name):
    package = importlib.import_module(package_name)
    path = getattr(package, '__path__', [])
    submodules = []

    for loader, name, is_pkg in pkgutil.walk_packages(path):
        full_name = f"{package_name}.{name}"
        submodules.append(full_name)

        if is_pkg:
            submodules.extend(list_submodules(full_name))

    return submodules

package_name = 'greed'
submodules = list_submodules(package_name)
modules_entry = ''

# use the alive_progress module to show progress bar
for submodule in submodules:
    CMD = "lazydocs " + submodule + " --output-path " + TARGET_FOLDER + " "
    CMD +=  "--src-base-url " + GITHUB_URL + " " + " --watermark "
    os.system(CMD)

    # if the file exists add it to the modules entry
    if os.path.exists(TARGET_FOLDER + submodule + ".md"):
        modules_entry += f"- {submodule}: modules/{submodule}.md\n    "


with open("./mkdocs_base.yml", "r") as f:
    lines = f.readlines()

new_lines = [] 
for line in lines:
    if "<AUTOMATICALLY_GENERATED>" in line:
        line = line.replace("<AUTOMATICALLY_GENERATED>", modules_entry)
    new_lines.append(line)

with open("./mkdocs_new.yml", "w") as f:
    f.writelines(new_lines)

