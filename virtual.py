import knormal as K
from ty import *
from typing import cast, Literal, List
from withbounds import WithBounds
from collections import ChainMap
import logging

logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)


class SSA:
    ...


class Mov(SSA):
    def __init__(self, dst: K.Id, src: K.KNormal):
        self.dst = dst
        self.src = src

    def __repr__(self):
        return f"{self.dst} = {self.src}"
