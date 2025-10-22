
from psycodict.database import PostgresDatabase
from .config import Configuration
db = PostgresDatabase(config=Configuration())
