
import os

import sqlalchemy as db
from sqlalchemy import Column, Integer, String, Boolean, Numeric, Text, Time, func, ForeignKey
from sqlalchemy.orm import Session, relationship
from sqlalchemy.orm import sessionmaker, scoped_session
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy import create_engine

Base = declarative_base()

# CONFIG 
PG_USER = os.environ.get('PG_USER', None)
PG_PASSWORD = os.environ.get('PG_PASSWORD', None)
PG_IP = os.environ.get('PG_IP', None)

if not PG_USER or not PG_PASSWORD or not PG_IP:
    print("Missing config to connect to DB")
    assert(False)

db_string_connection = f"postgresql://{PG_USER}:{PG_PASSWORD}@{PG_IP}/mainnet"

# MODELS 
class Transaction(Base):
    __tablename__ = "transactions"
    transaction_hash = Column(String, primary_key=True)
    sender = Column(String)
    receiver = Column(String)
    data = Column(Text)
    
class Trace(Base):
    __tablename__ = 'traces'
    id = Column(Integer, primary_key=True)
    transaction_hash = Column(String, index=True)
    sender = Column(String)
    receiver = Column(String)
    input = Column(Text)

# API
def get_n_transactions_to(contract_target, n, offset):
    engine = create_engine(db_string_connection)
    db_session = sessionmaker(engine)()
    transactions = db_session.query(Transaction).filter(Transaction.receiver == contract_target).offset(offset).limit(n).all()
    return transactions

