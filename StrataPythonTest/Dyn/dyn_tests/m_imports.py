# Each import form binds the fully qualified module or member.
import os
import os.path
import xml.etree.ElementTree as ET
import json as j
from collections.abc import Mapping as M
from math import pi

def local_import():
    import sys
    return sys
