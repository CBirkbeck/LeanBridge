
import os
import tempfile
import atexit
import shutil
from psycodict.config import Configuration as _Configuration

opj, ope = os.path.join, os.path.exists

class Configuration(_Configuration):
    def __init__(self):
        self.folder = tempfile.mkdtemp()
        self.options = self.default_args = {
            "postgresql": {
                "host": "devmirror.lmfdb.xyz",
                "user": "lmfdb",
                "password": "lmfdb",
                "dbname": "lmfdb",
                "port": "5432",
            },
            "logging": {
                "slowcutoff": 1000000, # Don't want slow warnings interactively
                "slowlogfile": opj(self.folder, "slow.log"), # currently, psycodict requires a log file, so we put it in a place that we can delete afterward
            }
        }
        self.extra_options = {}
        atexit.register(self.cleanup)

    def cleanup(self):
        if ope(self.folder):
            shutil.rmtree(self.folder)
